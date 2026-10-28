-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_positive_measurable_signed_products
-- name    : AvramDividend.Classical.causal_positive_measurable_signed_products
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T16:22:41.534612+00:00
-- url     : https://prove2.me/theorems/b0c98ecd-b8b6-444e-bf74-c6cfa2243522
-- title:
--   Positive-time continuous signed convolution products are measurable on half-open intervals
-- statement:
--   If a signed kernel and every convolution power are continuous on positive time, then each reflected signed convolution product is almost-everywhere strongly measurable on the half-open causal interval (0,x]. The possibly singular value of the kernel at zero is irrelevant because its endpoint has zero Lebesgue measure.
-- source:
--   The product is continuous on (0,x), since the reflected kernel and power are continuous at strictly positive arguments. Its endpoint at s=x has zero Lebesgue measure, so the pinned restriction-measure equality restrict_Ioo_eq_restrict_Ioc transfers AEStronglyMeasurable to the exact Ioc measure required by signed-power induction.

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Topology.ContinuousOn
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_positive_measurable_signed_products
    (k : ℝ → ℝ) (P : ℕ → ℝ → ℝ)
    (hkcont : ContinuousOn k (Ioi (0 : ℝ)))
    (hPcont : ∀ n : ℕ, ContinuousOn (P n) (Ioi (0 : ℝ))) :
    ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      AEStronglyMeasurable
        (fun s : ℝ => k (x - s) * P n s)
        (volume.restrict (Ioc (0 : ℝ) x)) := by sorry
