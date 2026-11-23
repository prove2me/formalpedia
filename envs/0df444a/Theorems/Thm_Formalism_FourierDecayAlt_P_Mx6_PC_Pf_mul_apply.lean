-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_Pf_mul_apply
-- name    : Formalism.FourierDecayAlt.P.Mx6.PC.Pf_mul_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:16:47.787437+00:00
-- url     : https://prove2.me/theorems/7ad4e293-74c4-43a9-b9f5-49b178254e6b
-- title:
--   PC: Pf mul apply
-- statement:
--   The PC construction uses the Pf mul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferRtt.lean#L1022-L1024
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferRtt.lean#L1022-L1024

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
variable (P : Par)
variable {B : Type} [Ring B]

theorem Formalism.FourierDecayAlt.P.Mx6.PC.Pf_mul_apply (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B) (i k : Fin 2) (p : Fin 2 × Fin 2) :
    (Pf B * X) (i, k) p = X (k, i) p := by sorry
