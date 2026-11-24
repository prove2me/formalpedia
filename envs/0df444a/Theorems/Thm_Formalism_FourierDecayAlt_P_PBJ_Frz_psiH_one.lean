-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBJ_Frz_psiH_one
-- name    : Formalism.FourierDecayAlt.P.PBJ.Frz.psiH_one
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:54:20.46427+00:00
-- url     : https://prove2.me/theorems/d2e5aa20-4fd7-46ab-8713-d3b4d2d90e8b
-- title:
--   Frz: psi H one
-- statement:
--   The Frz construction uses the psi H one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockTwoDiagonalZeroSize.lean#L136-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockTwoDiagonalZeroSize.lean#L136-L142

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

theorem Formalism.FourierDecayAlt.P.PBJ.Frz.psiH_one (β : ℂ) {p : ℕ} (σ : Equiv.Perm (Fin p)) (η : XiH p 1 σ) :
    psiH β σ η = G.psi β (subS (wP σ * lowW σ η.2.1 * (wP σ)⁻¹) + supS (G.upper η.2.2)) *
      G.psi β (cornerA η.1.1 + cornerB η.1.2) := by sorry
