-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_WB_model_root
-- name    : Formalism.FourierDecayAlt.P.Mx6.WB.model_root
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:30:50.677009+00:00
-- url     : https://prove2.me/theorems/4649d0c5-8bfb-47e2-a9d6-6a911a4edd78
-- title:
--   WB: model root
-- statement:
--   The WB construction uses the model root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferRtt.lean#L650-L723
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferRtt.lean#L650-L723

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx6 Formalism.FourierDecayAlt.P.Mx6.WB
open Matrix Finset Polynomial Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt
noncomputable section

theorem Formalism.FourierDecayAlt.P.Mx6.WB.model_root (P : Par) (hP : P.OK) (π : Ty P) (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) :
    (wNum P π /ₘ coordinatePolynomial P π).eval (-(rc P π l)) = (((Nrm P l π : ℝ) : ℂ) - ((NrmDown P l π : ℝ) : ℂ)) *
      ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rc P π j - rc P π l) := by sorry
