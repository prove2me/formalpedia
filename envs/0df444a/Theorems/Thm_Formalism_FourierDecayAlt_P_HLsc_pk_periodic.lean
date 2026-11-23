-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HLsc_pk_periodic
-- name    : Formalism.FourierDecayAlt.P.HLsc.pk_periodic
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:09:21.654553+00:00
-- url     : https://prove2.me/theorems/9e562fad-53ba-4e87-9577-905b4ed908fa
-- title:
--   HLsc: pk periodic
-- statement:
--   The HLsc construction uses the pk periodic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HerglotzLowerSemicontinuous.lean#L296-L302
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HerglotzLowerSemicontinuous.lean#L296-L302

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

theorem Formalism.FourierDecayAlt.P.HLsc.pk_periodic (y : Fin d → ℝ) (m : Fin d → ℤ) : pk (fun j => y j + (m j : ℝ)) = pk y := by sorry
