-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HLsc_integral_mul_normSq_tp
-- name    : Formalism.FourierDecayAlt.P.HLsc.integral_mul_normSq_tp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:46:53.431529+00:00
-- url     : https://prove2.me/theorems/922fb3ec-6035-400c-b4c9-0a3dc19df9d6
-- title:
--   HLsc: integral mul norm Sq tp
-- statement:
--   The HLsc construction uses the integral mul norm Sq tp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HerglotzLowerSemicontinuous.lean#L36-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HerglotzLowerSemicontinuous.lean#L36-L58

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Herglotz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HerglotzLowerSemicontinuous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HLsc
open Real Filter Topology Finset MeasureTheory Formalism.FourierDecayAlt.P.Herglotz
variable {d : ℕ}

theorem Formalism.FourierDecayAlt.P.HLsc.integral_mul_normSq_tp {W : (Fin d → ℝ) → ℝ} (hW : Integrable W)
    (B : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ) :
    ((∫ z, W z * ‖tp B c z‖ ^ 2 : ℝ) : ℂ) =
      ∑ σ ∈ B, ∑ σ' ∈ B, (∫ z, (W z : ℂ) * ee z (σ - σ')) * c σ * starRingEnd ℂ (c σ') := by sorry
