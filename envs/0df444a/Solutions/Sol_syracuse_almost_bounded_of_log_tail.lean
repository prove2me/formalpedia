-- Prove2me | solution 1 for syracuse_almost_bounded_of_log_tail
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-09T02:52:47.349639+00:00
-- url     : https://prove2.me/submissions/09bdffec-916e-42ae-a460-b84b3071746b

import Mathlib
import Definitions.Def_weightedLogMass
import Definitions.Def_syracuseOrbitMin
import Theorems.Thm_logarithmic_power_tail_threshold_reduction

open Filter
open scoped Topology

noncomputable section

theorem solution
    (f : ℕ → ℝ) (C c : ℝ) (hC : 0 < C) (hc : 0 < c)
    (hbound : ∀ M x : ℕ, 2 ≤ M → 2 ≤ x →
      weightedLogMass
        (fun n => 0 < n ∧ Odd n)
        (fun n => (M : ℝ) < (syracuseOrbitMin n : ℝ))
        (fun n => 1 / (n : ℝ)) x ≤
          C / Real.rpow (Real.log (M : ℝ)) c)
    (hf : Tendsto f atTop atTop) :
    Tendsto
      (fun x : ℕ =>
        weightedLogMass
          (fun n => 0 < n ∧ Odd n)
          (fun n => ¬ ∃ k : ℕ,
            ((syracuseStep^[k] n : ℕ) : ℝ) < f n)
          (fun n => 1 / (n : ℝ)) x)
      atTop (𝓝 0) := by
  classical
  let D : ℕ → Prop := fun n => 0 < n ∧ Odd n
  let w : ℕ → ℝ := fun n => 1 / (n : ℝ)
  let P : ℕ → ℝ := fun n => (syracuseOrbitMin n : ℝ)
  let E : ℕ → Prop := fun n => ¬ ∃ k : ℕ,
    ((syracuseStep^[k] n : ℕ) : ℝ) < f n
  have hw : ∀ k, 0 ≤ w k := by
    intro k
    dsimp [w]
    positivity
  have hbound' : ∀ M x : ℕ, 2 ≤ M → 2 ≤ x →
      weightedLogMass D (fun k => (M : ℝ) < P k) w x ≤
        C / Real.rpow (Real.log (M : ℝ)) c := by
    simpa [D, P, w] using hbound
  have htail := logarithmic_power_tail_threshold_reduction
    D w P f hw C c hC hc hbound' hf
  have hmin_attained : ∀ n : ℕ,
      ∃ k : ℕ, syracuseStep^[k] n = syracuseOrbitMin n := by
    intro n
    have hne :
        (Set.range (fun k : ℕ => syracuseStep^[k] n)).Nonempty :=
      ⟨n, ⟨0, Function.iterate_zero_apply syracuseStep n⟩⟩
    have hmem :
        sInf (Set.range (fun k : ℕ => syracuseStep^[k] n)) ∈
          Set.range (fun k : ℕ => syracuseStep^[k] n) :=
      Nat.sInf_mem hne
    exact hmem
  have hmin_le : ∀ (n k : ℕ),
      syracuseOrbitMin n ≤ syracuseStep^[k] n := by
    intro n k
    unfold syracuseOrbitMin
    exact Nat.sInf_le ⟨k, rfl⟩
  have hiff : ∀ n : ℕ, E n ↔ P n ≥ f n := by
    intro n
    constructor
    · intro hE
      apply le_of_not_gt
      intro hlt
      obtain ⟨k, hk⟩ := hmin_attained n
      apply hE
      refine ⟨k, ?_⟩
      rw [hk]
      exact hlt
    · intro hP hbad
      obtain ⟨k, hk⟩ := hbad
      have hle : P n ≤ ((syracuseStep^[k] n : ℕ) : ℝ) := by
        have hle' : (syracuseOrbitMin n : ℝ) ≤
            ((syracuseStep^[k] n : ℕ) : ℝ) := by
          exact_mod_cast hmin_le n k
        simpa [P] using hle'
      exact (not_lt_of_ge hP) (hle.trans_lt hk)
  have heq :
      (fun x : ℕ => weightedLogMass D E w x) =
        (fun x : ℕ => weightedLogMass D (fun n => P n ≥ f n) w x) := by
    funext x
    congr 2
    funext n
    exact propext (hiff n)
  change Tendsto (fun x : ℕ => weightedLogMass D E w x) atTop (𝓝 0)
  rw [heq]
  exact htail
