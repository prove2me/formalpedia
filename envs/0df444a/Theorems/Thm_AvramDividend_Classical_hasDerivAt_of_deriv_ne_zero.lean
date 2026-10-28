-- Prove2me | Theorems.Thm_AvramDividend_Classical_hasDerivAt_of_deriv_ne_zero
-- name    : AvramDividend.Classical.hasDerivAt_of_deriv_ne_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T19:43:49.421715+00:00
-- url     : https://prove2.me/theorems/23ad363d-f0d2-42ec-ad85-c050001816a1
-- title:
--   Differentiability from nonzero derivative
-- statement:
--   For a real function with nonzero derivative at a point, the function has HasDerivAt with its derivative. This is the differentiability bridge for barrierSupValue_eq_scale_ratio (a8d4c941), deriving hD from derivative positivity via contrapositive of deriv_zero_of_not_differentiableAt.
-- source:
--   Differentiability bridge helper for a8d4c941 barrierSupValue_eq_scale_ratio: HasDerivAt from nonzero deriv, isolating the contrapositive step used to obtain hD from scaleDeriv_pos

import Mathlib

open Filter Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem hasDerivAt_of_deriv_ne_zero {W : ℝ → ℝ} {a : ℝ} (hd : deriv W a ≠ 0) : HasDerivAt W (deriv W a) a := by sorry

end AvramDividend.Classical
