-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBJ_Frz_gI_ne
-- name    : Formalism.FourierDecayAlt.P.PBJ.Frz.gI_ne
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:53:33.403903+00:00
-- url     : https://prove2.me/theorems/e9558555-edfd-418e-ba01-0380ac992f48
-- title:
--   Frz: g I ne
-- statement:
--   The Frz construction uses the g I ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockTwoDiagonalZeroSize.lean#L264-L293
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockTwoDiagonalZeroSize.lean#L264-L293

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

theorem Formalism.FourierDecayAlt.P.PBJ.Frz.gI_ne {β c : ℂ} {p : ℕ} {Ψ : G.Mat (p + 1) → V} {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ)
    (hb : ∀ Z ∈ tsupport Ψ, ‖Z‖ ≤ R ∧ δ ≤ ‖G.detM Z‖) {H : G.Mat p} {y : AB p} (hne : gI β c Ψ H y ≠ 0) :
    H ∈ Sset p R (δ / ‖c‖) ∧ (∀ j, ‖(Matrix.of y.1 * Matrix.of H) 0 j‖ ≤ R) ∧
      ∀ i, ‖(Matrix.of H * Matrix.of y.2) i 0‖ ≤ R := by sorry
