-- Prove2me | solution 1 for syracuse_almost_bounded_logarithmic
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-09T04:01:38.084076+00:00
-- url     : https://prove2.me/submissions/acb64848-dc00-4620-920e-644844ff6c66
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under GPL-3.0-or-later as described in the file LICENSE.
Authors: Adam McKenna
-/

import Mathlib
import Definitions.Def_weightedLogMass
import Definitions.Def_weightedLogMassReal
import Definitions.Def_syracuseOrbitMin
import Theorems.Thm_logarithmic_power_tail_threshold_reduction
import Theorems.Thm_syracuse_uniform_logarithmic_tail_bound
import Theorems.Thm_odd_positive_logarithmic_density

open scoped BigOperators
open scoped Topology
open Filter
open Classical

noncomputable section

/-!
# Standalone conditional density-one-half Syracuse consumer

The published positive-odd normalization supplies the total mass `1/2`.
The generic logarithmic-tail reduction and the source-3.1 uniform tail mirror
supply zero exceptional mass.  The finite complement identity then proves the
successful-set conclusion.  No Solutions imports are used.
-/

theorem platform_weightedLogMass_nat_limit_to_real_zero
    (D E : ℕ → Prop) (w : ℕ → ℝ)
    (hw : ∀ k, 0 ≤ w k)
    (hlim : Tendsto (fun n : ℕ => weightedLogMass D E w n) atTop (𝓝 0)) :
    Tendsto (fun x : ℝ => weightedLogMassReal D E w x) atTop (𝓝 0) := by
  have hfloor : Tendsto (fun x : ℝ => ⌊x⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop
  have hcomp : Tendsto
      (fun x : ℝ => weightedLogMass D E w ⌊x⌋₊) atTop (𝓝 0) :=
    hlim.comp hfloor
  have hnonneg : ∀ᶠ x : ℝ in atTop, 0 ≤ weightedLogMassReal D E w x := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    unfold weightedLogMassReal
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro k hk
      split_ifs with h
      · exact hw k
      · exact le_rfl
    · exact (Real.log_pos (by linarith)).le
  have hupper : ∀ᶠ x : ℝ in atTop,
      weightedLogMassReal D E w x ≤ weightedLogMass D E w ⌊x⌋₊ := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    have hfloor_two : 2 ≤ ⌊x⌋₊ := by
      exact (Nat.le_floor_iff' (by omega : 2 ≠ 0)).2 (by exact_mod_cast hx)
    have hx_nonneg : (0 : ℝ) ≤ x := by linarith
    have hfloor_le : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx_nonneg
    have hfloor_pos : (0 : ℝ) < ⌊x⌋₊ := by
      exact_mod_cast (show 0 < ⌊x⌋₊ by omega)
    have hlog_floor : 0 < Real.log (⌊x⌋₊ : ℝ) := by
      exact Real.log_pos (by exact_mod_cast (show 1 < ⌊x⌋₊ by omega))
    have hlog_le : Real.log (⌊x⌋₊ : ℝ) ≤ Real.log x := by
      exact Real.log_le_log hfloor_pos hfloor_le
    unfold weightedLogMassReal weightedLogMass
    apply div_le_div_of_nonneg_left
    · apply Finset.sum_nonneg
      intro k hk
      split_ifs with h
      · exact hw k
      · exact le_rfl
    · exact hlog_floor
    · exact hlog_le
  exact squeeze_zero' hnonneg hupper hcomp

theorem platform_syracuseOrbitMin_attained (n : ℕ) :
    ∃ k : ℕ, syracuseStep^[k] n = syracuseOrbitMin n := by
  classical
  have hmem : syracuseOrbitMin n ∈
      Set.range (fun k : ℕ => syracuseStep^[k] n) := by
    unfold syracuseOrbitMin
    exact Nat.sInf_mem ⟨n, ⟨0, Function.iterate_zero_apply syracuseStep n⟩⟩
  exact hmem

theorem platform_syracuseOrbitMin_le_iterate (n k : ℕ) :
    syracuseOrbitMin n ≤ syracuseStep^[k] n := by
  classical
  unfold syracuseOrbitMin
  exact Nat.sInf_le ⟨k, rfl⟩

theorem platform_syracuseOrbitMin_lt_iff_exists_iterate_lt (n : ℕ) (b : ℝ) :
    (syracuseOrbitMin n : ℝ) < b ↔
      ∃ k : ℕ, ((syracuseStep^[k] n : ℕ) : ℝ) < b := by
  constructor
  · intro hmin
    obtain ⟨k, hk⟩ := platform_syracuseOrbitMin_attained n
    refine ⟨k, ?_⟩
    rw [hk]
    exact hmin
  · rintro ⟨k, hk⟩
    exact lt_of_le_of_lt
      (by exact_mod_cast platform_syracuseOrbitMin_le_iterate n k) hk

theorem solution
    (f : ℕ → ℝ)
    (hf : ∀ M : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (0 < n ∧ Odd n) → M < f n) :
    Tendsto
      (fun x : ℝ =>
        weightedLogMassReal
          (fun n => 0 < n ∧ Odd n)
          (fun n => ∃ k : ℕ,
            ((syracuseStep^[k] n : ℕ) : ℝ) < f n)
          (fun n => 1 / (n : ℝ)) x)
      atTop (𝓝 (1 / 2 : ℝ)) := by
  let D : ℕ → Prop := fun n => 0 < n ∧ Odd n
  let G : ℕ → Prop := fun n => ∃ k : ℕ,
    ((syracuseStep^[k] n : ℕ) : ℝ) < f n
  let B : ℕ → Prop := fun n => ¬ G n
  let w : ℕ → ℝ := fun n => 1 / (n : ℝ)
  have hbadNat : Tendsto
      (fun x : ℕ => weightedLogMass D (fun n =>
        (syracuseOrbitMin n : ℝ) ≥ f n) w x)
      atTop (𝓝 0) := by
    rcases syracuse_uniform_logarithmic_tail_bound with
      ⟨C, c, hC, hc, hbound⟩
    have hw : ∀ n : ℕ, 0 ≤ w n := by
      intro n
      dsimp [w]
      positivity
    have hboundNat : ∀ M x : ℕ, 2 ≤ M → 2 ≤ x →
        weightedLogMass D (fun n => (M : ℝ) < (syracuseOrbitMin n : ℝ)) w x ≤
          C / Real.rpow (Real.log (M : ℝ)) c := by
      intro M x hM hx
      have hM' : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      have hx' : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
      have h := hbound (M : ℝ) (x : ℝ) hM' hx'
      simpa [D, w, weightedLogMassReal, weightedLogMass] using h
    have hglobal : ∀ M : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → M <
        (if D n then f n else (n : ℝ)) := by
      intro M
      obtain ⟨Nf, hNf⟩ := hf M
      obtain ⟨Nn, hNn⟩ := exists_nat_gt M
      refine ⟨max Nf Nn, ?_⟩
      intro n hn
      by_cases hD : D n
      · simpa [hD] using hNf n (le_trans (le_max_left _ _) hn) hD
      · have hNn_le : Nn ≤ n := le_trans (le_max_right _ _) hn
        have hcast : (Nn : ℝ) ≤ (n : ℝ) := by exact_mod_cast hNn_le
        simpa [hD] using hNn.trans_le hcast
    let g : ℕ → ℝ := fun n => if D n then f n else (n : ℝ)
    have hg : Tendsto g atTop atTop := by
      refine tendsto_atTop.2 ?_
      intro M
      obtain ⟨N, hN⟩ := hglobal M
      filter_upwards [eventually_ge_atTop N] with n hn
      exact (hN n hn).le
    have hmain := logarithmic_power_tail_threshold_reduction
      D w (fun n => (syracuseOrbitMin n : ℝ)) g hw C c hC hc hboundNat hg
    have hmass : ∀ x : ℕ,
        weightedLogMass D (fun n => (syracuseOrbitMin n : ℝ) ≥ g n) w x =
          weightedLogMass D (fun n => (syracuseOrbitMin n : ℝ) ≥ f n) w x := by
      intro x
      unfold weightedLogMass
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hD : D k <;> simp [g, hD]
    have hfun :
        (fun x : ℕ => weightedLogMass D
          (fun n => (syracuseOrbitMin n : ℝ) ≥ g n) w x) =
          (fun x : ℕ => weightedLogMass D
            (fun n => (syracuseOrbitMin n : ℝ) ≥ f n) w x) := by
      funext x
      exact hmass x
    rw [hfun] at hmain
    exact hmain
  have hbadReal : Tendsto
      (fun x : ℝ => weightedLogMassReal D B w x)
      atTop (𝓝 0) := by
    have hiff : ∀ n : ℕ, B n ↔
        (syracuseOrbitMin n : ℝ) ≥ f n := by
      intro n
      constructor
      · intro hB
        apply le_of_not_gt
        intro hlt
        exact hB
          ((platform_syracuseOrbitMin_lt_iff_exists_iterate_lt n (f n)).mp hlt)
      · intro hP hG
        exact (not_lt_of_ge hP)
          ((platform_syracuseOrbitMin_lt_iff_exists_iterate_lt n (f n)).mpr hG)
    have hpred : B = (fun n => (syracuseOrbitMin n : ℝ) ≥ f n) := by
      funext n
      exact propext (hiff n)
    rw [hpred]
    exact platform_weightedLogMass_nat_limit_to_real_zero D
      (fun n => (syracuseOrbitMin n : ℝ) ≥ f n) w
      (by intro n; dsimp [w]; positivity) hbadNat
  have htotal : Tendsto
      (fun x : ℝ => weightedLogMassReal D (fun _ => True) w x)
      atTop (𝓝 (1 / 2 : ℝ)) := by
    simpa [D, w] using odd_positive_logarithmic_density
  have hpartition : ∀ x : ℝ,
      weightedLogMassReal D G w x + weightedLogMassReal D B w x =
        weightedLogMassReal D (fun _ => True) w x := by
    intro x
    unfold weightedLogMassReal
    rw [← add_div]
    congr 1
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hD : D k
    · by_cases hG : G k
      · simp [hD, hG, B]
      · simp [hD, hG, B]
    · simp [hD]
  have hdiff := htotal.sub hbadReal
  have hgood : Tendsto
      (fun x : ℝ => weightedLogMassReal D G w x)
      atTop (𝓝 ((1 / 2 : ℝ) - 0)) := by
    apply hdiff.congr'
    filter_upwards [] with x
    have hp := hpartition x
    linarith
  simpa [D, G, w] using hgood
