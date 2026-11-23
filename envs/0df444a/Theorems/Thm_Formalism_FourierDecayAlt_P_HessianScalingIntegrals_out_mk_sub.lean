-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HessianScalingIntegrals_out_mk_sub
-- name    : Formalism.FourierDecayAlt.P.HessianScalingIntegrals.out_mk_sub
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:09:52.384688+00:00
-- url     : https://prove2.me/theorems/648ed57b-11ec-49f5-a79d-5dfff1c671ff
-- title:
--   Hessian Scaling Integrals: out mk sub
-- statement:
--   The Hessian Scaling Integrals construction uses the out mk sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HessianScalingIntegrals.lean#L11-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HessianScalingIntegrals.lean#L11-L14

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

theorem Formalism.FourierDecayAlt.P.HessianScalingIntegrals.out_mk_sub (Λ : AddSubgroup K) (x : K) :
    (Quotient.out (x : K ⧸ Λ) : K) - x ∈ Λ := by sorry
