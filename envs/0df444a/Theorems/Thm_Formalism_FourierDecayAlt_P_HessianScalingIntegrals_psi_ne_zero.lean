-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HessianScalingIntegrals_psi_ne_zero
-- name    : Formalism.FourierDecayAlt.P.HessianScalingIntegrals.psi_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:09:47.980799+00:00
-- url     : https://prove2.me/theorems/fd9b77ed-25b7-42db-9d50-36ca318e979a
-- title:
--   Hessian Scaling Integrals: psi ne zero
-- statement:
--   The Hessian Scaling Integrals construction uses the psi ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HessianScalingIntegrals.lean#L134-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HessianScalingIntegrals.lean#L134-L138

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HessianScalingIntegrals
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HessianScalingIntegrals
variable {K : Type} [CommRing K]

theorem Formalism.FourierDecayAlt.P.HessianScalingIntegrals.psi_ne_zero (ψ : AddChar K ℂ) (a : K) : ψ a ≠ 0 := by sorry
