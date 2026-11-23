-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_L4_T_ne
-- name    : Formalism.FourierDecayAlt.P.Mx6.L4.T_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:29:58.757806+00:00
-- url     : https://prove2.me/theorems/c62a8ccb-e94c-4746-9340-b94ae3d5c5d9
-- title:
--   L4: T ne
-- statement:
--   The L4 construction uses the T ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferRtt.lean#L1320-L1326
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferRtt.lean#L1320-L1326

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx6 Formalism.FourierDecayAlt.P.Mx6.L4
open Matrix Finset Polynomial Formalism.FourierDecayAlt.M
noncomputable section
variable (P : Par)

theorem Formalism.FourierDecayAlt.P.Mx6.L4.T_ne {u : ℂ} (hu : Good P u) {l j : ℕ} (hj : j ∈ Icc 1 (P.k - 1)) (hne : j ≠ l) :
    (kap P fun π => xEx P {l} π u) * star (SS P l) * (kap P (rr P j u) * SS P j) =
      star (SS P l) * SS P j * kap P fun π => xEx P {l, j} π u := by sorry
