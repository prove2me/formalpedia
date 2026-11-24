-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBJ_Frz_block_two_one_lower_zero
-- name    : Formalism.FourierDecayAlt.P.PBJ.Frz.block_two_one_lower_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:05:57.545984+00:00
-- url     : https://prove2.me/theorems/ff0afceb-e9ab-48a3-84ac-8f9e991b9538
-- title:
--   Frz: block two one lower zero
-- statement:
--   The Frz construction uses the block two one lower zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockTwoDiagonalZeroSize.lean#L22-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockTwoDiagonalZeroSize.lean#L22-L31

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

theorem Formalism.FourierDecayAlt.P.PBJ.Frz.block_two_one_lower_zero {p : ℕ} (a : Fin 0 → Fin p → ℂ) :
    (blk2 (1 : Matrix (Fin p) (Fin p) ℂ) 0 (Matrix.of a) 1 : Matrix (Fin (p + 0)) (Fin (p + 0)) ℂ) = 1 := by sorry
