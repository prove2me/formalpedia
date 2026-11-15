-- Prove2me | Theorems.Thm_CurrentAFT_RationalFullResponseProgram_choiceAverage_bound
-- name    : CurrentAFT.RationalFullResponseProgram.choiceAverage_bound
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T21:18:04.601796+00:00
-- url     : https://prove2.me/theorems/4d852c28-eb8b-4b42-83f3-af671595380f
-- title:
--   Uniform bound for the actual without-replacement full response
-- statement:
--   For every security parameter, order at least one with twice the order at most the security parameter, integer queue, full-response source index, bijective block-to-vertex layout, truncated arity, primary colors and safe body centers, the absolute actual family data of the without-replacement choice-averaged response is at most the public root bound. The statement uses the actual finite choice law and its normalized average; its bound is uniform over all listed choices.
-- source:
--   Original public theorem choiceAverage_bound from CurrentAFT/RationalFullResponseAverages.lean. Its complete proof and all required mathematical helpers are extracted from the original Lean syntax/kernel dependency graph. This theorem node splits the existing full full-response matrix error proof into two independently checked packages, retaining the exact original target metadata.

import Definitions.Def_InfoLossLAR_NativeBundle_12
import Mathlib
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

theorem _root_.CurrentAFT.RationalFullResponseProgram.choiceAverage_bound (security order : ℕ) (horder : 1 ≤ order) (hroom : 2*order ≤ security) (queue : ℤ)
    (source : _root_.CurrentAFT.FullResponsePointFormula.Index security order) (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) (colors : Fin arity.val.1.val → _root_.CurrentAFT.FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → _root_.CurrentAFT.ActualControls.SafePalette security) :
    |_root_.CurrentAFT.RationalActualFamilyApproximation.data security order (_root_.CurrentAFT.FullResponseWeightedIdentity.choiceAverage security order horder hroom queue source layout)
      arity colors centers| ≤ _root_.CurrentAFT.RationalFullResponseProgram.rootBound security order := by sorry
