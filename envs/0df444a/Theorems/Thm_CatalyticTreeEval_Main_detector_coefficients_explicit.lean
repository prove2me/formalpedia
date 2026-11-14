-- Prove2me | Theorems.Thm_CatalyticTreeEval_Main_detector_coefficients_explicit
-- name    : CatalyticTreeEval.Main.detector_coefficients_explicit
-- status  : Proved
-- author  : @sragavan
-- created : 2026-11-14T02:35:19.05429+00:00
-- url     : https://prove2.me/theorems/a33e7c0b-79c6-4038-8140-9fe96f844cd6
-- title:
--   Explicit binomial inverse for prime-power detector coefficients
-- statement:
--   For positive $q$ and arbitrary modulus $p$, let $r=w\bmod q$. The coefficient of elementary symmetric degree $j<q$ in the inverse-Pascal detector specification equals
--
--   $$c_j=\mathbf1_{j=0}-\mathbf1_{r\le j}(-1)^{j-r}\binom jr\quad\text{in }\mathbb Z/p\mathbb Z.$$
--
--   This identifies the algebraic matrix-inverse specification with the explicit formula used for streamed coefficients. No primality hypothesis is needed for the identity itself.
-- source:
--   Henzinger, Pyne and Ragavan, Catalytic Tree Evaluation from Matching Vectors, https://arxiv.org/html/2602.14320v3, Appendix B, Lemma B.5.

import Definitions.Def_CatalyticTreeEval_DetectorCoefficients

set_option autoImplicit false

namespace CatalyticTreeEval.Main

theorem detector_coefficients_explicit (p q w : ℕ) (hq : 0 < q) :
    detectorCoefficients p q w = explicitDetectorCoefficient p q w := by sorry

end CatalyticTreeEval.Main
