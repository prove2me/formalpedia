-- Prove2me | solution 1 for levy_foundations_pointFamilySplitIndep
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T00:10:23.433312+00:00
-- url     : https://prove2.me/submissions/06cadb3b-e4c9-464c-aa0c-6c0bf17a7c3d

import Mathlib.Probability.Independence.Process.Basic
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
    {S T : Type*} (φ : S → ℕ ⊕ ℕ × ℕ) (ψ : T → ℕ ⊕ ℕ × ℕ)
    (hφ : Function.Injective φ) (hψ : Function.Injective ψ)
    (hST : ∀ s t, φ s ≠ ψ t) :
    IndepFun (fun ω (i : S) => LevyFoundations.pointFamilyCombined K X (φ i) ω)
      (fun ω (j : T) => LevyFoundations.pointFamilyCombined K X (ψ j) ω) μ := by
  classical
  have hcoord : ∀ i, Measurable (LevyFoundations.pointFamilyCombined K X i)
    | Sum.inl k => hd.measurable_count k
    | Sum.inr p => hd.measurable_point p.1 p.2
  refine IndepFun.process_indepFun_process (fun i => hcoord (φ i))
    (fun j => hcoord (ψ j)) ?_
  intro I J
  set eφ : S ↪ ℕ ⊕ ℕ × ℕ := ⟨φ, hφ⟩
  set eψ : T ↪ ℕ ⊕ ℕ × ℕ := ⟨ψ, hψ⟩
  have hdisj : Disjoint (I.map eφ) (J.map eψ) := by
    rw [Finset.disjoint_left]
    rintro x hx1 hx2
    rw [Finset.mem_map] at hx1 hx2
    obtain ⟨a, -, rfl⟩ := hx1
    obtain ⟨c, -, hc⟩ := hx2
    exact hST a c hc.symm
  have key := hd.indep.indepFun_finset (I.map eφ) (J.map eψ) hdisj hcoord
  have hLmeas : Measurable
      (fun (g : (i : ↑(I.map eφ)) →
          LevyFoundations.pointFamilyIndexType E i.1) (i : I) =>
        g ⟨φ i, Finset.mem_map_of_mem eφ i.2⟩) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply _
  have hRmeas : Measurable
      (fun (g : (j : ↑(J.map eψ)) →
          LevyFoundations.pointFamilyIndexType E j.1) (j : J) =>
        g ⟨ψ j, Finset.mem_map_of_mem eψ j.2⟩) :=
    measurable_pi_lambda _ fun j => measurable_pi_apply _
  exact key.comp hLmeas hRmeas
