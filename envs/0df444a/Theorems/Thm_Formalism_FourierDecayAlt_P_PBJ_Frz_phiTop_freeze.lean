-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBJ_Frz_phiTop_freeze
-- name    : Formalism.FourierDecayAlt.P.PBJ.Frz.phiTop_freeze
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:51:07.343829+00:00
-- url     : https://prove2.me/theorems/b31185c9-7d23-4cfd-b4ef-787890c1ebbd
-- title:
--   Frz: phi Top freeze
-- statement:
--   The Frz construction uses the phi Top freeze property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockTwoDiagonalZeroSize.lean#L149-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockTwoDiagonalZeroSize.lean#L149-L179

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

theorem Formalism.FourierDecayAlt.P.PBJ.Frz.phiTop_freeze [CompleteSpace V] (β c : ℂ) {p : ℕ} (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ)
    (hd : ∀ i, d i ≠ 0) {Ψ : G.Mat (p + 1) → V} (hΨ : KCls Ψ) :
    PhiTop (p := p) (s := 1) β σ d Ψ (fun _ _ => c) =
      PhiTop (p := p) (s := 0) β σ d (Psc β c Ψ) (fun x => x.elim0) := by sorry
