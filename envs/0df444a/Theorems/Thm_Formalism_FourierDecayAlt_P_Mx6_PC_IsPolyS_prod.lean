-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPolyS_prod
-- name    : Formalism.FourierDecayAlt.P.Mx6.PC.IsPolyS.prod
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:07:55.138091+00:00
-- url     : https://prove2.me/theorems/a23d2e9c-2342-4cb3-9044-9081a7861d59
-- title:
--   Is Poly S: prod
-- statement:
--   The Is Poly S construction uses the prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferRtt.lean#L876-L880
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferRtt.lean#L876-L880

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx6 Formalism.FourierDecayAlt.P.Mx6.PC
open Matrix Finset Polynomial Formalism.FourierDecayAlt.M Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W
noncomputable section
variable {B : Type*} [Ring B] [Algebra ℂ B]

theorem Formalism.FourierDecayAlt.P.Mx6.PC.IsPolyS.prod {ι : Type*} (s : Finset ι) {a : ι → ℂ → ℂ} (ha : ∀ i ∈ s, IsPolyS (a i)) :
    IsPolyS fun y => ∏ i ∈ s, a i y := by sorry
