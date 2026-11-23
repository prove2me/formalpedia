-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz3_log_one_add_sub
-- name    : Formalism.FourierDecayAlt.P.Sz3.log_one_add_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:18.964722+00:00
-- url     : https://prove2.me/theorems/300bd7a3-7e17-4d08-a483-db3bcc59582b
-- title:
--   Sz3: log one add sub
-- statement:
--   The Sz3 construction uses the log one add sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/VandermondeRatioHarmonic.lean#L133-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/VandermondeRatioHarmonic.lean#L133-L152

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_VandermondeRatioHarmonic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz3
open Finset Formalism.FourierDecayAlt.Sz

theorem Formalism.FourierDecayAlt.P.Sz3.log_one_add_sub (x : ℝ) (hx : |x| ≤ 1 / 4) : |Real.log (1 + x) - x| ≤ 2 / 3 * x ^ 2 := by sorry
