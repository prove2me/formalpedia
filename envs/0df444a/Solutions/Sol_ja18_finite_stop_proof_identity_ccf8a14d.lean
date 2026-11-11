-- Prove2me | solution 1 for ja18_finite_stop_proof_identity_ccf8a14d
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T21:30:18.14997+00:00
-- url     : https://prove2.me/submissions/983a24f3-f6b8-4dd6-81c2-9a54efc53a9a

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (J : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0) (T : ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτT : ∀ ω, τ ω ≤ T)
    (F : Finset ℝ≥0) (hτF : ∀ ω, τ ω ∈ F)
    (hInt : ∀ t, Integrable (J t) P)
    (hMart : ∀ s t : ℝ≥0, s ≤ t →
      ∀ᵐ ω ∂P, condExp (𝓕.rightCont s) P (J t) ω = J s ω)
    (hZero : ∀ᵐ ω ∂P, J 0 ω = 0) 
    (hf : (let f : ℝ≥0 → Ω → ℝ := fun t => P[J t | 𝓕.rightCont t]; Martingale f 𝓕.rightCont P))
    (hτBound : (let f : ℝ≥0 → Ω → ℝ := fun t => P[J t | 𝓕.rightCont t]; ∀ ω, (τ ω : WithTop ℝ≥0) ≤ (T : WithTop ℝ≥0)))
    : (let f : ℝ≥0 → Ω → ℝ := fun t => P[J t | 𝓕.rightCont t]; (Set.range (fun ω => (τ ω : WithTop ℝ≥0))).Countable) := by
    classical
    let f : ℝ≥0 → Ω → ℝ := fun t => P[J t | 𝓕.rightCont t]
    have hSubset : Set.range (fun ω => (τ ω : WithTop ℝ≥0)) ⊆
        (↑(F.image (fun t : ℝ≥0 => (t : WithTop ℝ≥0))) : Set (WithTop ℝ≥0)) := by
      rintro a ⟨ω, rfl⟩
      exact Finset.mem_coe.mpr
        (Finset.mem_image.mpr ⟨τ ω, hτF ω, rfl⟩)
    exact (Finset.finite_toSet (F.image
      (fun t : ℝ≥0 => (t : WithTop ℝ≥0)))).countable.mono hSubset
end
