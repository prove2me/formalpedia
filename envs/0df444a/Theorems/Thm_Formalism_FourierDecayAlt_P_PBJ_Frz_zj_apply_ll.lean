-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBJ_Frz_zj_apply_ll
-- name    : Formalism.FourierDecayAlt.P.PBJ.Frz.zj_apply_ll
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:05:43.37735+00:00
-- url     : https://prove2.me/theorems/81d1f129-e634-46d3-b417-99c7f66e1a22
-- title:
--   Frz: zj apply ll
-- statement:
--   The Frz construction uses the zj apply ll property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockTwoDiagonalZeroSize.lean#L189-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockTwoDiagonalZeroSize.lean#L189-L192

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KloostDensOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopCellsOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnitaryInvariantGaussian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockTwoDiagonalZeroSize
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBJ Formalism.FourierDecayAlt.P.PBJ.Frz
open MeasureTheory Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Formalism.FourierDecayAlt.P.PBJ.Frz.zj_apply_ll {p : ℕ} (a : Fin 1 → Fin p → ℂ) (b : Fin p → Fin 1 → ℂ) (H : Matrix (Fin p) (Fin p) ℂ)
    (C : Matrix (Fin 1) (Fin 1) ℂ) (i j : Fin p) : Zj a b H C (Fin.castAdd 1 i) (Fin.castAdd 1 j) = H i j := by sorry
