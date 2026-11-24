-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBJ_Frz_zj_zero
-- name    : Formalism.FourierDecayAlt.P.PBJ.Frz.zj_zero
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:52:39.376696+00:00
-- url     : https://prove2.me/theorems/e2f366af-c42f-4cff-b158-a24c372cc417
-- title:
--   Frz: zj zero
-- statement:
--   The Frz construction uses the zj zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockTwoDiagonalZeroSize.lean#L56-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockTwoDiagonalZeroSize.lean#L56-L59

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

theorem Formalism.FourierDecayAlt.P.PBJ.Frz.zj_zero {p : ℕ} (a : Fin 0 → Fin p → ℂ) (b : Fin p → Fin 0 → ℂ) (H : Matrix (Fin p) (Fin p) ℂ)
    (Z : Matrix (Fin 0) (Fin 0) ℂ) : (Zj a b H Z : Matrix (Fin (p + 0)) (Fin (p + 0)) ℂ) = H := by sorry
