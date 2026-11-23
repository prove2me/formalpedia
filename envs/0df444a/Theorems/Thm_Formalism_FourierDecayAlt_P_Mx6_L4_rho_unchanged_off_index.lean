-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_L4_rho_unchanged_off_index
-- name    : Formalism.FourierDecayAlt.P.Mx6.L4.rho_unchanged_off_index
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:29:58.128193+00:00
-- url     : https://prove2.me/theorems/40cc2173-89ff-420a-add8-b4777f8fc1dc
-- title:
--   L4: rho unchanged off index
-- statement:
--   The L4 construction uses the rho unchanged off index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferRtt.lean#L1280-L1283
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferRtt.lean#L1280-L1283

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

theorem Formalism.FourierDecayAlt.P.Mx6.L4.rho_unchanged_off_index {i j : ℕ} (hj : j ∈ Icc 1 (P.k - 1)) (hne : j ≠ i) {π π' : Ty P} (h : Up P i π π') (u : ℂ) :
    rr1 P j u π' = rr1 P j u π := by sorry
