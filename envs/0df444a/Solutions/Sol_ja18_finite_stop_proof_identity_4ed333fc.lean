-- Prove2me | solution 1 for ja18_finite_stop_proof_identity_4ed333fc
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T21:54:18.960641+00:00
-- url     : https://prove2.me/submissions/30b59934-87a4-4619-a65b-a31b5746e5b4

import Mathlib.Probability.Martingale.Basic
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
    (hCount : (let f : ℝ≥0 → Ω → ℝ := fun t => P[J t | 𝓕.rightCont t]; (Set.range (fun ω => (τ ω : WithTop ℝ≥0))).Countable))
    (hAt : (let f : ℝ≥0 → Ω → ℝ := fun t => P[J t | 𝓕.rightCont t]; (∀ (ω : Ω), stoppedValue f (fun ω => (τ ω : WithTop ℝ≥0)) ω =
        f (τ ω) ω)))
    : (let f : ℝ≥0 → Ω → ℝ := fun t => P[J t | 𝓕.rightCont t]; ∀ᵐ ω ∂P, ∀ t ∈ F, f t ω = J t ω) := by
    classical
    let f : ℝ≥0 → Ω → ℝ := fun t => P[J t | 𝓕.rightCont t]
    have hInd (S : Finset ℝ≥0) :
        ∀ᵐ ω ∂P, ∀ t ∈ S, f t ω = J t ω := by
      induction S using Finset.induction_on with
      | empty =>
          filter_upwards [] with ω t ht
          simp at ht
      | @insert t S hnot ih =>
          filter_upwards [hMart t t le_rfl, ih] with ω ht hS u hu
          rcases Finset.mem_insert.mp hu with rfl | hs
          · exact ht
          · exact hS u hs
    exact hInd F
end
