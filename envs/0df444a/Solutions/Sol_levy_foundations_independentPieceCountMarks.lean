-- Prove2me | solution 1 for levy_foundations_independentPieceCountMarks
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:33:41.257871+00:00
-- url     : https://prove2.me/submissions/22b4af06-ff35-43c6-87c1-7131536716d7

import Mathlib.Probability.Independence.Basic
import Definitions.Def_levy_foundations_isPoissonPointFamily

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (m : Measure E) [SigmaFinite m]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E)
    (hd : LevyFoundations.IsPoissonPointFamily K X m μ)
    (k : ℕ) :
    IndepFun (K k) (fun ω n => X k n ω) μ := by
  classical
  have hmeas : ∀ i, Measurable (LevyFoundations.pointFamilyCombined K X i)
    | Sum.inl j => hd.measurable_count j
    | Sum.inr p => hd.measurable_point p.1 p.2
  have hsplit : IndepFun
      (fun ω (_ : Unit) =>
        LevyFoundations.pointFamilyCombined K X (Sum.inl k) ω)
      (fun ω n =>
        LevyFoundations.pointFamilyCombined K X (Sum.inr (k, n)) ω) μ := by
    refine IndepFun.process_indepFun_process
      (fun _ => hd.measurable_count k)
      (fun n => hd.measurable_point k n) ?_
    intro I J
    set eφ : Unit ↪ ℕ ⊕ ℕ × ℕ :=
      ⟨fun _ => Sum.inl k, fun _ _ _ => rfl⟩
    set eψ : ℕ ↪ ℕ ⊕ ℕ × ℕ :=
      ⟨fun n => Sum.inr (k, n), fun a b hab => by simpa using hab⟩
    have hdisj : Disjoint (I.map eφ) (J.map eψ) := by
      rw [Finset.disjoint_left]
      rintro x hx1 hx2
      rw [Finset.mem_map] at hx1 hx2
      obtain ⟨a, -, rfl⟩ := hx1
      obtain ⟨c, -, hc⟩ := hx2
      exact (by cases hc)
    have key := hd.indep.indepFun_finset
      (I.map eφ) (J.map eψ) hdisj hmeas
    have hLmeas : Measurable
        (fun (g : (i : ↑(I.map eφ)) →
            LevyFoundations.pointFamilyIndexType E i.1) (i : I) =>
          g ⟨Sum.inl k, Finset.mem_map_of_mem eφ i.2⟩) :=
      measurable_pi_lambda _ fun i => measurable_pi_apply _
    have hRmeas : Measurable
        (fun (g : (j : ↑(J.map eψ)) →
            LevyFoundations.pointFamilyIndexType E j.1) (j : J) =>
          g ⟨Sum.inr (k, j.1), Finset.mem_map_of_mem eψ j.2⟩) :=
      measurable_pi_lambda _ fun j => measurable_pi_apply _
    exact key.comp hLmeas hRmeas
  exact hsplit.comp (φ := fun g : Unit → ℕ => g ()) (ψ := id)
    (measurable_pi_apply _) measurable_id
