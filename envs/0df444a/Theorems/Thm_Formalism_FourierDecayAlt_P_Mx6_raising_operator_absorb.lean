-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_raising_operator_absorb
-- name    : Formalism.FourierDecayAlt.P.Mx6.raising_operator_absorb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:32:59.516223+00:00
-- url     : https://prove2.me/theorems/0d6a3fba-6bd3-4be1-8683-3c8b857c876c
-- title:
--   Mx6: raising operator absorb
-- statement:
--   The Mx6 construction uses the raising operator absorb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferRtt.lean#L240-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferRtt.lean#L240-L246

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

theorem Formalism.FourierDecayAlt.P.Mx6.raising_operator_absorb (Ns cz g G X Ls : B) (α : ℂ)
    (hNsg : Ns * g = g * Ns - g * cz) (hNsX : Ns * X = X * Ns) (hGg : G * g = 1) (hczg : cz * g = g * cz)
    (hczX : cz * X = X * cz) (hLsg : Ls * g = g * Ls) :
    (-Ns - α • cz + G * Ls) * (g * X) = g * X * (-Ns - (α - 1) • cz) + Ls * X := by sorry
