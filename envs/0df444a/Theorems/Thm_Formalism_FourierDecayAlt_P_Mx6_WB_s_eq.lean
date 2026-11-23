-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_WB_s_eq
-- name    : Formalism.FourierDecayAlt.P.Mx6.WB.s_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:31:07.19699+00:00
-- url     : https://prove2.me/theorems/8d3589db-f154-44c6-9cd1-4b52e2e6d37f
-- title:
--   WB: s eq
-- statement:
--   The WB construction uses the s eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferRtt.lean#L725-L740
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferRtt.lean#L725-L740

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

theorem Formalism.FourierDecayAlt.P.Mx6.WB.s_eq (P : Par) (hP : P.OK) (π : Ty P) :
    (q1P P).nextCoeff - ∑ i ∈ Icc 1 (P.k - 1), (rc P π i + 1) - ∑ i ∈ Icc 1 (P.k - 1), rc P π i =
      1 + 2 * (aC P π : ℂ) := by sorry
