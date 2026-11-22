-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_compensated_kernel_volume_integrable_of_shifted_integrable
-- name    : AvramDividend.Classical.esscher_compensated_kernel_volume_integrable_of_shifted_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T08:27:20.488306+00:00
-- url     : https://prove2.me/theorems/8b87003a-fe0c-458b-bb9a-b7da15638722
-- title:
--   Esscher compensated kernel explicitly Lebesgue integrable from shifted finite tails
-- statement:
--   When both original compensated Lévy-tail kernels at φ+s and φ are Lebesgue integrable over positive jump magnitudes, the Esscher-weighted kernel exp(−φt)(1−exp(−st))κ(t) is also integrable. This is the finite-real-integral difference identity, retaining cancellation for infinitely many small jumps. It is a prerequisite for constructing the killed Bernstein Lévy measure from the source original Lévy exponent-to-tail identity. Explicit volume measure arguments fix missing MeasureSpace ℝ instances.
-- source:
--   Exact exponential addition identity, Mathlib Integrable.sub; complements Proved Esscher tail integral shift 3ed689c3 and original killed Bernstein 0cb20c38; target 2fa29eaf.

import Mathlib
open MeasureTheory Set

theorem AvramDividend.Classical.esscher_compensated_kernel_volume_integrable_of_shifted_integrable
    (κ : ℝ → ℝ) (φ s : ℝ)
    (hNext : IntegrableOn
      (fun t : ℝ => (1 - Real.exp (-((φ + s) * t))) * κ t) (Ioi 0) (volume : Measure ℝ))
    (hBase : IntegrableOn
      (fun t : ℝ => (1 - Real.exp (-(φ * t))) * κ t) (Ioi 0) (volume : Measure ℝ)) :
    IntegrableOn
      (fun t : ℝ => Real.exp (-(φ * t)) *
        (1 - Real.exp (-(s * t))) * κ t) (Ioi 0) (volume : Measure ℝ) := by sorry
