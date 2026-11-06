-- Prove2me | Theorems.Thm_BianchiIX_coreGrowthPrimitive_difference
-- name    : BianchiIX.coreGrowthPrimitive_difference
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T00:34:43.427455+00:00
-- url     : https://prove2.me/theorems/75466862-6c17-4b71-8daf-3d0c6479c833
-- title:
--   A uniform bound for increments of the growth primitive
-- statement:
--   For real $k,z$, define
--   $$\Gamma_k(z)=2\arctan(\sinh z)+\frac{24}{10000k}z,
--   \qquad C_* = \exp\left(2\pi+\frac{48}{10000}\right).$$
--   Division at zero has its total real-field meaning.
--   If $k\geq6$ and
--   $|a|,|b|\leq\log(4k)$, then
--   $$\Gamma_k(b)-\Gamma_k(a)\leq2\pi+48/10000.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/CoreGrowthBudget.lean#L32-L48

import Definitions.Def_BianchiIX_Analysis_CoreGrowthBudget
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
open BianchiIX

theorem BianchiIX.coreGrowthPrimitive_difference {k a b : ℝ} (hk : 6 ≤ k)
    (ha : |a| ≤ Real.log (4 * k)) (hb : |b| ≤ Real.log (4 * k)) :
    coreGrowthPrimitive k b - coreGrowthPrimitive k a ≤ 2 * Real.pi + 48 / 10000 := by sorry
