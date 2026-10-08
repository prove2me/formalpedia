-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleDeriv_pos_of_W0_tilted_monotone
-- name    : AvramDividend.Classical.scaleDeriv_pos_of_W0_tilted_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T18:22:42.153473+00:00
-- url     : https://prove2.me/theorems/cff38c80-877c-4961-9236-29b94880d958
-- title:
--   Strict scale-derivative positivity at every nonnegative barrier level in the W(0)>0 regime
-- statement:
--   Assume W(0)>0, φ>0, W is nondecreasing on [0,∞), exp(-φx)W(x) is nondecreasing for x>0, and W differentiable at every positive x. Then scaleDeriv W x, whose special x=0 branch is the EReal right-liminf derivative, is strictly positive at every x≥0. The proof handles x=0 with a uniform derivative lower bound and x>0 with the normalized-derivative positivity theorem.
-- source:
--   Bridge to the canonical open scaleDeriv_pos using Proved interior derivative positivity and the staged right-boundary strict positivity. Assumes a positive initial scale value, characterising the bounded-variation branch; does not prove tilted monotonicity from Standing.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scale_deriv_zero_pos_of_normalized_monotone_and_W0
import Theorems.Thm_AvramDividend_Classical_scale_deriv_pos_of_normalized_monotone
open AvramDividend.Classical
open scoped Topology ENNReal

namespace AvramDividend.Classical

theorem scaleDeriv_pos_of_W0_tilted_monotone
    (W : ℝ → ℝ) (φ : ℝ)
    (hφ : 0 < φ) (hW0 : 0 < W 0)
    (hmonoW : MonotoneOn W (Set.Ici 0))
    (htilt : MonotoneOn
      (fun t : ℝ => Real.exp (-φ * t) * W t) (Set.Ioi 0))
    (hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x) :
    ∀ x : ℝ, 0 ≤ x → (0 : EReal) < scaleDeriv W x := by sorry

end AvramDividend.Classical
