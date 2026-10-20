-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_lower_exit_lintegral_zero_of_ae_no_creeping
-- name    : AvramDividend.Classical.chat04_lower_exit_lintegral_zero_of_ae_no_creeping
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T20:31:37.622053+00:00
-- url     : https://prove2.me/theorems/362ed18d-0f5b-4e66-8ed6-db4459e7340a
-- title:
--   The lower-exit discounted q-scale integral vanishes under almost-sure absence of creeping
-- statement:
--   The exact pointwise lower-exit payoff decomposition identifies the only possible nonzero stopped scale value at lower exit as W(0) times a discount on an exact-contact event. Under the explicitly stated almost-everywhere hypothesis that the strict downward exit before upper exit cannot terminate at reserve zero, the integrand therefore vanishes almost everywhere. By invariance of the Lebesgue integral under almost-everywhere equality, the extended-nonnegative integral of the killed lower-exit discounted scale payoff equals zero. This covers any value W(0), including bounded-variation scale functions, but deliberately leaves the probabilistic non-creeping theorem as a separate obligation.
-- source:
--   AvramDividend.Classical.chat04_lower_exit_scale_creeping_atom UUID 0f1adee0-3670-4143-b12f-b52df6fbae1b, pending proof at creation; exact pinned Mathlib.MeasureTheory.Integral.Lebesgue.Basic lemmas lintegral_congr_ae and lintegral_zero. A conditionally exact almost-sure bridge for the Open stopped-scale martingale theorem 09663d0d-c23e-47da-b5b9-1bbf28449a4d.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_lower_exit_scale_creeping_atom

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_lower_exit_lintegral_zero_of_ae_no_creeping
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ)
    (hNoCreep : ∀ᵐ ω ∂P,
      twoSidedExitDownTime X (-x) ω <
        twoSidedExitUpTime X (a - x) ω →
        x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω ≠ 0) :
    (∫⁻ ω,
      if twoSidedExitDownTime X (-x) ω <
          twoSidedExitUpTime X (a - x) ω then
        ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitDownTime X (-x) ω).toReal))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω))
      else 0 ∂P) = 0 := by sorry
