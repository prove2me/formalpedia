-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ProductFactorBounds_factor_bounds_first
-- name    : Formalism.FourierDecayAlt.P.ProductFactorBounds.factor_bounds_first
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:35:46.28704+00:00
-- url     : https://prove2.me/theorems/336830a4-54db-4cba-a0ef-3e7e041ca310
-- title:
--   Product Factor Bounds: factor bounds first
-- statement:
--   The Product Factor Bounds construction uses the factor bounds first property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ProductFactorBounds.lean#L124-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ProductFactorBounds.lean#L124-L145

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ProductFactorBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ProductFactorBounds
open Formalism.FourierDecayAlt.F7

theorem Formalism.FourierDecayAlt.P.ProductFactorBounds.factor_bounds_first (N : ℝ) (hN : 2 ≤ N) (l : WLetter ℝ) (Y : ℝ)
    (h : N ^ 2 ≤ |Y - l.pt|) (hf : l.first = true) :
    1 - 1 / (N ^ 2 - 1) ^ 2 ≤ wFactor l Y ∧ wFactor l Y ≤ 1 + 0 := by sorry
