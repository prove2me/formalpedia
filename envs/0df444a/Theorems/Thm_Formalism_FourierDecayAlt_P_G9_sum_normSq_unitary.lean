-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G9_sum_normSq_unitary
-- name    : Formalism.FourierDecayAlt.P.G9.sum_normSq_unitary
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:15.437219+00:00
-- url     : https://prove2.me/theorems/fa279f96-220a-413c-9558-6f73dbc3970d
-- title:
--   G9: sum norm Sq unitary
-- statement:
--   The G9 construction uses the sum norm Sq unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussianHessianIntegral.lean#L341-L353
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussianHessianIntegral.lean#L341-L353

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G MeasureTheory Matrix Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G9

theorem Formalism.FourierDecayAlt.P.G9.sum_normSq_unitary {d : ℕ} {U : Matrix (Fin d) (Fin d) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (x : Fin d → ℂ) :
    ∑ k, ‖(U *ᵥ x) k‖ ^ 2 = ∑ k, ‖x k‖ ^ 2 := by sorry
