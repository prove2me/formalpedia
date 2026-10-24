-- Prove2me | Theorems.Thm_AvramDividend_Classical_continuousOn_positive_causal_convolution_of_locally_bounded_integrable
-- name    : AvramDividend.Classical.continuousOn_positive_causal_convolution_of_locally_bounded_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:04:27.093921+00:00
-- url     : https://prove2.me/theorems/c039e3d8-3d03-4f1a-85f9-c4de9e3b5260
-- title:
--   Positive-time continuity of the convolution of causal L1 kernels with local tail bounds
-- statement:
--   Let f,g be integrable real kernels supported on strictly positive time, continuous on (0,∞), and bounded on every tail [ε,∞). Then their additive convolution x↦∫f(y)g(x−y)dy is continuous for x>0. The kernels may diverge integrably at zero. This is the missing recursive continuity theorem for the BV Esscher renewal densities k_n, since k_n need not be monotone for n>1.
-- source:
--   Classical continuity of convolution of locally bounded causal L1 functions away from time zero; split the integral near y=0 and y=x and use local dominated convergence on the middle interval. Apply to renewal convolution densities in the BV absolutely continuous Lévy case.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Convolution
open MeasureTheory Set

namespace AvramDividend.Classical
theorem continuousOn_positive_causal_convolution_of_locally_bounded_integrable
    (f g : ℝ → ℝ)
    (hfint : Integrable f volume) (hgint : Integrable g volume)
    (hfcont : ContinuousOn f (Ioi (0 : ℝ)))
    (hgcont : ContinuousOn g (Ioi (0 : ℝ)))
    (hfzero : ∀ x : ℝ, x ≤ 0 → f x = 0)
    (hgzero : ∀ x : ℝ, x ≤ 0 → g x = 0)
    (hfbound : ∀ ε : ℝ, 0 < ε →
      ∃ M : ℝ, ∀ x : ℝ, ε ≤ x → |f x| ≤ M)
    (hgbound : ∀ ε : ℝ, 0 < ε →
      ∃ M : ℝ, ∀ x : ℝ, ε ≤ x → |g x| ≤ M) :
    ContinuousOn (fun x : ℝ =>
      ∫ y : ℝ, f y * g (x - y) ∂volume) (Ioi 0) := by sorry
end AvramDividend.Classical
