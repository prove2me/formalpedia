-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_L3_ee_off_diagonal_second
-- name    : Formalism.FourierDecayAlt.P.Mx6.L3.ee_off_diagonal_second
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:30:01.141802+00:00
-- url     : https://prove2.me/theorems/fc978162-f1d6-47ca-9df7-9a9a414dbb2a
-- title:
--   L3: ee off diagonal second
-- statement:
--   The L3 construction uses the ee off diagonal second property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferRtt.lean#L1182-L1193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferRtt.lean#L1182-L1193

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx6 Formalism.FourierDecayAlt.P.Mx6.L3
open Matrix Finset Polynomial Formalism.FourierDecayAlt.M
noncomputable section
variable (P : Par)

theorem Formalism.FourierDecayAlt.P.Mx6.L3.ee_off_diagonal_second {i j : ℕ} (hi : i ∈ Icc 1 (P.k - 1)) (hj : j ∈ Icc 1 (P.k - 1)) (hne : j ≠ i)
    (u v : ℂ) (hu : Good P u) (hv : Good P v) :
    ee P j i u v = -(cc P i j u v * fun π => (rho P π j : ℂ) - (rho P π i : ℂ) - 1) := by sorry
