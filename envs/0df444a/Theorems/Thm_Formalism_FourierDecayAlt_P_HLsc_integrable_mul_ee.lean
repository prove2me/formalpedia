-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HLsc_integrable_mul_ee
-- name    : Formalism.FourierDecayAlt.P.HLsc.integrable_mul_ee
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:09:06.850811+00:00
-- url     : https://prove2.me/theorems/17e5a79c-39f6-4b41-afda-f8f19cab0b32
-- title:
--   HLsc: integrable mul ee
-- statement:
--   The HLsc construction uses the integrable mul ee property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HerglotzLowerSemicontinuous.lean#L31-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HerglotzLowerSemicontinuous.lean#L31-L34

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

theorem Formalism.FourierDecayAlt.P.HLsc.integrable_mul_ee {W : (Fin d → ℝ) → ℝ} (hW : Integrable W) (σ : Fin d → ℤ) :
    Integrable (fun z => (W z : ℂ) * ee z σ) := by sorry
