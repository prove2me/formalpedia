-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_xEx_split
-- name    : Formalism.FourierDecayAlt.P.Mx6.xEx_split
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:13:09.174944+00:00
-- url     : https://prove2.me/theorems/c34f5ac1-304b-41db-abb2-ce8b7109e45f
-- title:
--   Mx6: x Ex split
-- statement:
--   The Mx6 construction uses the x Ex split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferRtt.lean#L102-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferRtt.lean#L102-L108

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
open Matrix Finset Polynomial Formalism.FourierDecayAlt.M
noncomputable section
variable (P : Par)

theorem Formalism.FourierDecayAlt.P.Mx6.xEx_split (π : Ty P) (u : ℂ) {l j : ℕ} (hj : j ∈ Icc 1 (P.k - 1)) (hlj : j ≠ l) :
    xEx P {l} π u = (u + (rho P π j : ℂ)) * xEx P {l, j} π u := by sorry
