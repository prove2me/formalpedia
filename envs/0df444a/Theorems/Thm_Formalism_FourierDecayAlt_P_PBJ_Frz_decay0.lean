-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBJ_Frz_decay0
-- name    : Formalism.FourierDecayAlt.P.PBJ.Frz.decay0
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:54:58.544597+00:00
-- url     : https://prove2.me/theorems/5e02d95b-242d-4040-aa22-9b6d9aac783a
-- title:
--   Frz: decay0
-- statement:
--   The Frz construction uses the decay0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockTwoDiagonalZeroSize.lean#L90-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockTwoDiagonalZeroSize.lean#L90-L121

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

theorem Formalism.FourierDecayAlt.P.PBJ.Frz.decay0 {n : ℕ} {Ψ : G.Mat n → V} (hΨ : KCls Ψ) (E : ℝ) (hE : 0 ≤ E) :
    ∃ K : ℝ, DecayAll 0 (fun _ => E) K Ψ := by sorry
