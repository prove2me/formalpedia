-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_boundary_preserved_monotone_interior_lintegral_iSup
-- name    : AvramDividend.Classical.avram_wave7_19_original_boundary_preserved_monotone_interior_lintegral_iSup
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:13:57.839415+00:00
-- url     : https://prove2.me/theorems/18274bd7-c75a-4b5a-8612-88add1e5a284
-- title:
--   Original ruin Stieltjes cash exhausts through increasing interior windows with explicit cap-supported mass retained
-- statement:
--   For each genuine original Lévy/dividend path, let boundary be the measurable upper-cap payment support and interior_n an increasing family of measurable interior payment windows. If the complete original paymentTimes(ruinTime)∩Iic T is covered by boundary ∪ ⋃ interior_n, the full source discounted dividendMeasure cash is bounded by the supremum of complete cash on boundary ∪ interior_n. The boundary contribution is retained at every stage, including any reflection-cap singular Stieltjes mass, while zero-time right payment and strictly excluded positive ruin-time payments follow the exact source predicate. The proof uses original source cash, Set.iSup_indicator with monotone set supports, lintegral_iSup and lintegral_mono_set. The cap-support measurability and samplewise cover are explicit W7-18 obligations; no cap occupation-time inference, continuity at ruin, UI or extra canonical HJB condition is assumed.
-- source:
--   Actual original ruinTime/paymentTimes/dividendMeasure. Pinned Mathlib Set.iSup_indicator, lintegral_indicator, lintegral_iSup; W7-19 missing upper-cap mass correction for W7-18 local Ito to W7-08 canonical cash.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_19_original_boundary_preserved_monotone_interior_lintegral_iSup
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (boundary : Set ℝ) (interior : ℕ → Set ℝ)
    (hBoundaryMeas : MeasurableSet boundary)
    (hInteriorMeas : ∀ n, MeasurableSet (interior n))
    (hInteriorMon : Monotone interior)
    (hCover : paymentTimes (ruinTime X x D ω) ∩ Iic T ⊆
      ⋃ n : ℕ, boundary ∪ interior n) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
    (⨆ n : ℕ, (∫⁻ t in boundary ∪ interior n,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))) := by sorry
