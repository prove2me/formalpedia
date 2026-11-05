-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_raw_weighted_martingale_step
-- name    : AvramDividend.Classical.avram_p4_g_isometry_original_raw_weighted_martingale_step
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:18:58.377606+00:00
-- url     : https://prove2.me/theorems/2113499e-60e0-4b63-b161-42cfab6accc6
-- title:
--   Original intrinsic finite-band compensated predictable cell is a raw-filtration martingale difference
-- statement:
--   For the actual Lévy jump count on original Ω and F, an L2 predictable weighted finite negative-band compensated cell preserves the conditional expectation of any integrable F_s-measurable prefix. Uses the exact original P2-E rectangle law and explicit source measurability and L2 hypotheses. This is a finite-cell original martingale-step theorem, without auxiliary Poisson measure, right-continuous augmentation, infinite-band limit or stopping.
-- source:
--   P4-G weighted conditional mean theorem plus pinned Mathlib condExp_add and condExp_of_stronglyMeasurable for actual raw source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_raw_weighted_condExp_zero

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_g_isometry_original_raw_weighted_martingale_step
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (ε : ℝ) (hε : 0 < ε) (B : Set ℝ)
    (hB : MeasurableSet B) (hBand : B ⊆ Ioo (-1 : ℝ) (-ε))
    (hν : X.ν B < ⊤)
    (N : Ω → ℝ≥0∞)
    (hActual : N = fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B))
    (hMeas : Measurable N)
    (hRect : ∀ A : Set Ω, MeasurableSet[𝓕 s] A →
      (∫⁻ ω in A, N ω ∂P) =
        P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)
    (H : Ω → ℝ)
    (hH : StronglyMeasurable[𝓕 s] H)
    (hHL2 : MemLp H 2 P)
    (hCountL2 : MemLp (fun ω => (N ω).toReal -
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) 2 P)
    (M : Ω → ℝ)
    (hM : StronglyMeasurable[𝓕 s] M)
    (hMInt : Integrable M P)
    : P[(fun ω => M ω + H ω * ((N ω).toReal -
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal)) | 𝓕 s]
        =ᵐ[P] M := by sorry
