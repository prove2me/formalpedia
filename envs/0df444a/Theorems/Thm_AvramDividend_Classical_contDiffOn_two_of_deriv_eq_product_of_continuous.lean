-- Prove2me | Theorems.Thm_AvramDividend_Classical_contDiffOn_two_of_deriv_eq_product_of_continuous
-- name    : AvramDividend.Classical.contDiffOn_two_of_deriv_eq_product_of_continuous
-- status  : Open
-- author  : @WillR
-- created : 2026-10-21T22:17:34.979513+00:00
-- url     : https://prove2.me/theorems/f6a251b4-12fe-41e6-860e-ee2a8567d853
-- title:
--   Twice continuous differentiability of a function whose derivative is a product with a function of vanishing derivative
-- statement:
--   Let W and g be real functions that are continuous on the positive half-line, and suppose that the derivative of W at every positive point is the product of W with g there, that is W is differentiable with W' = W g on the positive axis. Suppose in addition that g has vanishing derivative at every positive point. Then W is twice continuously differentiable on the positive half-line, with second derivative W g squared. This is the elementary assembly step that turns a fluctuation identity of the form W' = W g into a C2 regularity statement: the derivative of W is the continuous function W g, the derivative of that is W g^2 because g' = 0, and W g^2 is continuous. The statement is the second-derivative step of the Brownian-smoothing regularity of the scale function in the Gaussian branch of the mission, where the excursion-height measure is atomless and the logarithmic derivative of the Esscher-tilted scale function therefore has vanishing derivative.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Levy process, arXiv:math/0702893v1, eq. (3.3) and the Lemma 4 discussion: the q-scale function is C2 on the positive axis when the Gaussian coefficient is positive, because the excursion-height measure is atomless.

import Mathlib

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem contDiffOn_two_of_deriv_eq_product_of_continuous
    (W g : ℝ → ℝ)
    (hWcont : ContinuousOn W (Ioi (0 : ℝ)))
    (hgcont : ContinuousOn g (Ioi (0 : ℝ)))
    (hderiv : ∀ x : ℝ, 0 < x → HasDerivAt W (W x * g x) x)
    (hgzero : ∀ x : ℝ, 0 < x → deriv g x = 0) :
    ContDiffOn ℝ 2 W (Ioi (0 : ℝ)) := by sorry

end AvramDividend.Classical
