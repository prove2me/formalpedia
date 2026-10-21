-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_restrictedMass_measurable
-- name    : AvramDividend.Classical.runningSup_restrictedMass_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T08:22:25.39069+00:00
-- url     : https://prove2.me/theorems/331155d2-26dd-4a42-ae9b-5b5e46827a1c
-- title:
--   Total random interval-restricted running-supremum Stieltjes mass is measurable
-- statement:
--   For the true spectrally negative Lévy running-supremum dividend Stieltjes measure restricted to an arbitrary fixed half-open interval, the total mass is a measurable ENNReal-valued random variable. It follows from the proved random measure-valued measurability theorem and the pinned Giry-measure evaluation measurability at the universally measurable set. The result supplies measurable sample-mass level sets required for a countable decomposition into uniformly finite kernels.
-- source:
--   Remotely proved runningSup_dividendMeasure_restrict_Ioc_measurable target d763694e-e35d-43bf-90d6-3d1a42a067ed; pinned remote compiler MeasureTheory.Measure.measurable_coe signature job d3e058c6-5f1b-4ebc-ab2c-9d44813a53ee.

import Mathlib.MeasureTheory.Measure.GiryMonad
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_restrict_Ioc_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.runningSup_restrictedMass_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s t : ℝ) :
    Measurable (fun ω : Ω =>
      ((dividendMeasure (runningSup X) ω).restrict (Set.Ioc s t)) Set.univ) := by sorry
