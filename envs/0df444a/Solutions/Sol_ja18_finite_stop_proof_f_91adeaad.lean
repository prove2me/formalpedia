-- Prove2me | solution 1 for ja18_finite_stop_proof_f_91adeaad
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T21:59:45.178485+00:00
-- url     : https://prove2.me/submissions/4a9f961c-18bd-41b4-93f4-b100db513e98

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
    : (let f : ℝ≥0 → Ω → ℝ := fun t => P[J t | 𝓕.rightCont t]; Martingale f 𝓕.rightCont P) := by
    classical
    let f : ℝ≥0 → Ω → ℝ := fun t => P[J t | 𝓕.rightCont t]
    constructor
    · intro t
      exact stronglyMeasurable_condExp
    · intro s t hst
      change P[P[J t | 𝓕.rightCont t] | 𝓕.rightCont s] =ᵐ[P]
        P[J s | 𝓕.rightCont s]
      have hSame : (P[J t | 𝓕.rightCont s]) =ᵐ[P]
          (P[J s | 𝓕.rightCont s]) := by
        filter_upwards [hMart s t hst, hMart s s le_rfl] with ω ht hs
        exact ht.trans hs.symm
      exact (condExp_condExp_of_le (𝓕.rightCont.mono hst)
        (𝓕.rightCont.le t)).trans hSame
end
