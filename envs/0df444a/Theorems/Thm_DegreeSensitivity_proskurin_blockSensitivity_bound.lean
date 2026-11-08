-- Prove2me | Theorems.Thm_DegreeSensitivity_proskurin_blockSensitivity_bound
-- name    : DegreeSensitivity.proskurin_blockSensitivity_bound
-- status  : Open
-- author  : @queelius
-- created : 2026-11-07T16:51:51.423227+00:00
-- url     : https://prove2.me/theorems/6a323834-cdc5-4dd6-ad1a-b7416d62c4e3
-- title:
--   Proskurin's constant: $(\sqrt{10}-2)\,bs(f) \le \deg(f)^2$
-- statement:
--   For every Boolean function $f$ whose degree is not 1, $(\sqrt{10}-2)\, bs(f) \le \deg(f)^2$. Degree-1 functions (literals) are excluded because they violate the inequality.
-- source:
--   N. V. Proskurin, On separation between the degree of a Boolean function and the block sensitivity, arXiv:2101.08600 (2021), Theorem 1. The paper states it for all Boolean functions; a single literal (degree 1, block sensitivity 1) is a counterexample, so the hypothesis deg f != 1 is added (it excludes exactly the degree-1 functions).

import Definitions.Def_BoolFunc
import Definitions.Def_blockSensitivity
import Definitions.Def_polyDegree
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace DegreeSensitivity

theorem proskurin_blockSensitivity_bound {n : ℕ} (f : BoolFunc n) (hdeg : polyDegree f ≠ 1) :
    (Real.sqrt 10 - 2) * (blockSensitivity f : ℝ) ≤ (polyDegree f : ℝ) ^ 2 := by sorry

end DegreeSensitivity
