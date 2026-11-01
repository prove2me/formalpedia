-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_p1_actual_source_stopped_signed_jump_compensation_of_rectangles
-- name    : AvramDividend.Classical.avram_wave5_p1_actual_source_stopped_signed_jump_compensation_of_rectangles
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T00:51:34.765068+00:00
-- url     : https://prove2.me/theorems/f544dab9-21ae-4ce6-b2a1-1c4041802831
-- title:
--   Original Lévy stopped signed jump reward has zero compensator discrepancy under source rectangle and Fubini laws
-- statement:
--   On the original SpectrallyNegativeLevy X and its unchanged sample space Ω, NX(ω) is fixed pointwise to the literal intrinsic jump measure of X built from X(t)-X(t-). Suppose M is the expected source marked measure and N the intensity candidate, verified by explicit source Fubini representation and the elementary predictable adapted-rectangle equalities, with a finite-mass mark-band exhaustion. Any integrable predictable mark kernel G stopped at the actual filtration stopping time τ has an integrable source jump reward whose expectation equals its N-compensator integral, hence exactly zero discrepancy. The theorem does not assume full Campbell equality or a Poisson copy. The source Fubini and rectangle conditions remain genuine independent obligations; it does not prove them from Lévy axioms.
-- source:
--   Bridge from Proved sigma-finite stopped L1 predictable marked Campbell transfer UUID 80ae40da-4b55-4e4b-bc4c-621f4d994dfa to literal original SpectrallyNegativeLevy jump paths. Its hFuture/hBot correspond to still-Open source predictable rectangle theorem 393b03a8-2e9a-43d8-b415-854d86d58104 owned by Chat 01. Same original source, no copy independence. Intended for Chat 03 controlled Itô–Meyer and Chat 05 UBV verification.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_sigma_stopped_predictable_marked_l1_transfer

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_p1_actual_source_stopped_signed_jump_compensation_of_rectangles
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, NX ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 =>
          (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (M N : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (B : ℕ → Set ℝ) (hBm : ∀ k, MeasurableSet (B k))
    (hBmono : Monotone B) (hBcover : (⋃ k, B k) = Set.univ)
    (hLocal : ∀ k, M ((Set.univ : Set (ℝ≥0 × Ω)) ×ˢ B k) ≠ ∞)
    (hBot : ∀ (A : Set Ω) (C : Set ℝ),
      MeasurableSet[𝓕 ⊥] A → MeasurableSet C →
      M (({(⊥ : ℝ≥0)} ×ˢ A) ×ˢ C) =
        N (({(⊥ : ℝ≥0)} ×ˢ A) ×ˢ C))
    (hFuture : ∀ (i : ℝ≥0) (A : Set Ω) (C : Set ℝ),
      MeasurableSet[𝓕 i] A → MeasurableSet C →
      M ((Set.Ioi i ×ˢ A) ×ˢ C) =
        N ((Set.Ioi i ×ˢ A) ×ˢ C))
    (τ : Ω → ℝ≥0∞) (hτ : IsStoppingTime 𝓕 τ)
    (G : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hGm : Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.predictable) (inferInstance : MeasurableSpace ℝ))] G)
    (hGi : Integrable G M)
    (H : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hH : H = fun p =>
      if (p.1.1 : ℝ≥0∞) ≤ τ p.1.2 then G p else 0)
    (hActualI : Integrable
      (fun ω => ∫ p, H ((p.1, ω), p.2) ∂(NX ω)) P)
    (hSourceFubini :
      (∫ ω, ∫ p, H ((p.1, ω), p.2) ∂(NX ω) ∂P) =
        ∫ p, H p ∂M) :
    Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.predictable) (inferInstance : MeasurableSpace ℝ))] H ∧
    Integrable H M ∧ Integrable H N ∧
      (∫ ω, ∫ p, H ((p.1, ω), p.2) ∂(NX ω) ∂P) -
        (∫ p, H p ∂N) = 0 := by sorry
