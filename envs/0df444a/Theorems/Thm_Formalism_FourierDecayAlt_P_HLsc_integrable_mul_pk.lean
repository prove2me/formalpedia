-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HLsc_integrable_mul_pk
-- name    : Formalism.FourierDecayAlt.P.HLsc.integrable_mul_pk
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:08:53.457812+00:00
-- url     : https://prove2.me/theorems/7d6bdb72-b434-4b83-b409-bad38b6682e3
-- title:
--   HLsc: integrable mul pk
-- statement:
--   The HLsc construction uses the integrable mul pk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HerglotzLowerSemicontinuous.lean#L333-L338
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HerglotzLowerSemicontinuous.lean#L333-L338

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

theorem Formalism.FourierDecayAlt.P.HLsc.integrable_mul_pk {N : (Fin d → ℝ) → ℝ} (hint : Integrable N) (z₀ : Fin d → ℝ) (n : ℕ) :
    Integrable (fun z => N z * pk (z - z₀) ^ n) := by sorry
