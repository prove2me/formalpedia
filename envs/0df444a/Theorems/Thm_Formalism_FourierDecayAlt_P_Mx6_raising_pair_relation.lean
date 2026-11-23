-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_raising_pair_relation
-- name    : Formalism.FourierDecayAlt.P.Mx6.raising_pair_relation
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:33:08.978285+00:00
-- url     : https://prove2.me/theorems/42cd42c2-4ab2-4fad-8ea2-f3fb8b1a663e
-- title:
--   Mx6: raising pair relation
-- statement:
--   The Mx6 construction uses the raising pair relation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferRtt.lean#L206-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferRtt.lean#L206-L218

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx6
variable {B : Type*} [Ring B] [Algebra ℂ B]

theorem Formalism.FourierDecayAlt.P.Mx6.raising_pair_relation (N c G L L' : B) (α β : ℂ)
    (hNc : N * c = c * N - c * c) (hNG : N * G = G * N - c * G)
    (hNL : N * L = L * N - c * L) (hNL' : N * L' = L' * N - c * L')
    (hGc : G * c = c * G) (hLc : L * c = c * L) (hLc' : L' * c = c * L')
    (hLG : L * G = G * L) (hLG' : L' * G = G * L')
    (h3 : (α - β) • (L * L' - L' * L) = (L - L') * (L - L')) :
    (α - β) • ((-N - α • c + G * L) * (-N - β • c + G * L') - (-N - β • c + G * L') * (-N - α • c + G * L)) =
      ((-N - α • c + G * L) - (-N - β • c + G * L')) * ((-N - α • c + G * L) - (-N - β • c + G * L')) := by sorry
