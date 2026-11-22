-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G6_rpow_bound
-- name    : Formalism.FourierDecayAlt.P.G6.rpow_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:09:54.024425+00:00
-- url     : https://prove2.me/theorems/ac8231bd-f9e7-405b-842f-07a44243f6f7
-- title:
--   G6: rpow bound
-- statement:
--   The G6 construction uses the rpow bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RemainderNormLeStrictUpper.lean#L180-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RemainderNormLeStrictUpper.lean#L180-L189

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G6
open Formalism.FourierDecayAlt.G

theorem Formalism.FourierDecayAlt.P.G6.rpow_bound (m : ℕ) {T ε : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hε : ε ≤ 1 / (2 * ((m : ℝ) + 2))) : (T ^ (-ε)) ^ (m + 2) * T ≤ Real.sqrt T := by sorry
