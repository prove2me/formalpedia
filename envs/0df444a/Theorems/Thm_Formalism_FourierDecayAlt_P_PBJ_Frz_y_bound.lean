-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBJ_Frz_y_bound
-- name    : Formalism.FourierDecayAlt.P.PBJ.Frz.y_bound
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:54:44.562068+00:00
-- url     : https://prove2.me/theorems/ca130a34-f6f0-4342-aa79-1ad970c12cc9
-- title:
--   Frz: y bound
-- statement:
--   The Frz construction uses the y bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockTwoDiagonalZeroSize.lean#L303-L337
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockTwoDiagonalZeroSize.lean#L303-L337

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

theorem Formalism.FourierDecayAlt.P.PBJ.Frz.y_bound {β c : ℂ} {p : ℕ} {Ψ : G.Mat (p + 1) → V} {R δ M : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) (hc : c ≠ 0)
    (hb : ∀ Z ∈ tsupport Ψ, ‖Z‖ ≤ R ∧ δ ≤ ‖G.detM Z‖) (hM0 : 0 ≤ M)
    (hM : ∀ H ∈ Sset p R (δ / ‖c‖), ∀ i j, ‖((Matrix.of H)⁻¹ : Matrix (Fin p) (Fin p) ℂ) i j‖ ≤ M)
    {H : G.Mat p} {y : AB p} (hne : gI β c Ψ H y ≠ 0) : ‖y‖ ≤ p * R * M := by sorry
