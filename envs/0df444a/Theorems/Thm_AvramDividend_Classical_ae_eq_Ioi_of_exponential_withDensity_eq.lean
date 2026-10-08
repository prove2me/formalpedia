-- Prove2me | Theorems.Thm_AvramDividend_Classical_ae_eq_Ioi_of_exponential_withDensity_eq
-- name    : AvramDividend.Classical.ae_eq_Ioi_of_exponential_withDensity_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T21:51:33.2933+00:00
-- url     : https://prove2.me/theorems/f897c25f-2acb-4a9c-a487-0f2b5a8231a2
-- title:
--   Almost-everywhere identification from equal exponential density measures
-- statement:
--   If two nonnegative functions on the positive half-line produce the same measure after multiplication by the same strictly positive exponential weight and application of ENNReal.ofReal, then the original functions agree almost everywhere on the positive half-line. No continuity is needed.
-- source:
--   Extracted from the already-accepted proof of continuousOn_Ioi_eq_of_exponential_withDensity_eq. The proof uses withDensity_eq_iff_of_sigmaFinite, positivity of the exponential factor, ENNReal.ofReal injectivity on nonnegative reals, and cancellation of the nonzero exponential.

import Mathlib
open MeasureTheory Filter Set Topology
open scoped ENNReal

namespace AvramDividend.Classical

theorem ae_eq_Ioi_of_exponential_withDensity_eq
    (f g : ℝ → ℝ) (B : ℝ)
    (hfnonneg : ∀ x : ℝ, 0 < x → 0 ≤ f x)
    (hgnonneg : ∀ x : ℝ, 0 < x → 0 ≤ g x)
    (hfdens : AEMeasurable
      (fun x : ℝ => ENNReal.ofReal (Real.exp (-B * x) * f x))
      (volume.restrict (Ioi 0)))
    (hgdens : AEMeasurable
      (fun x : ℝ => ENNReal.ofReal (Real.exp (-B * x) * g x))
      (volume.restrict (Ioi 0)))
    (hmeas :
      (volume.restrict (Ioi 0)).withDensity
          (fun x : ℝ => ENNReal.ofReal (Real.exp (-B * x) * f x)) =
        (volume.restrict (Ioi 0)).withDensity
          (fun x : ℝ => ENNReal.ofReal (Real.exp (-B * x) * g x))) :
    f =ᵐ[volume.restrict (Ioi 0)] g := by
  sorry

end AvramDividend.Classical
