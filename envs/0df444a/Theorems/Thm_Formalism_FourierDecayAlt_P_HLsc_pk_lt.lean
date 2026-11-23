-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HLsc_pk_lt
-- name    : Formalism.FourierDecayAlt.P.HLsc.pk_lt
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:09:12.232895+00:00
-- url     : https://prove2.me/theorems/39fc9a2f-efad-4240-ab50-874ce840c3b2
-- title:
--   HLsc: pk lt
-- statement:
--   The HLsc construction uses the pk lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HerglotzLowerSemicontinuous.lean#L267-L294
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HerglotzLowerSemicontinuous.lean#L267-L294

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

theorem Formalism.FourierDecayAlt.P.HLsc.pk_lt (y : Fin d → ℝ) (hy : y ∈ cube d) (hy0 : y ≠ 0) : pk y < pk (0 : Fin d → ℝ) := by sorry
