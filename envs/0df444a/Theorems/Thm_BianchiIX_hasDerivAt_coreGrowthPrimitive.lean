-- Prove2me | Theorems.Thm_BianchiIX_hasDerivAt_coreGrowthPrimitive
-- name    : BianchiIX.hasDerivAt_coreGrowthPrimitive
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T00:34:30.547204+00:00
-- url     : https://prove2.me/theorems/7cae2681-4e1c-4da0-b9d0-13392eca508d
-- title:
--   The derivative of the angular growth primitive
-- statement:
--   For real $k,z$, define
--   $$\Gamma_k(z)=2\arctan(\sinh z)+\frac{24}{10000k}z,
--   \qquad C_* = \exp\left(2\pi+\frac{48}{10000}\right).$$
--   Division at zero has its total real-field meaning.
--   For all real $k,z$,
--   $$\Gamma_k'(z)=\frac2{\cosh z}+\frac{24}{10000k}.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/CoreGrowthBudget.lean#L18-L24

import Definitions.Def_BianchiIX_Analysis_CoreGrowthBudget
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
open BianchiIX

theorem BianchiIX.hasDerivAt_coreGrowthPrimitive (k z : ℝ) :
    HasDerivAt (coreGrowthPrimitive k) (2 / Real.cosh z + 24 * ((1 / 10000) / k)) z := by sorry
