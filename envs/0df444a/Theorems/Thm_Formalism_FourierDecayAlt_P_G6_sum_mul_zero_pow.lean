-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G6_sum_mul_zero_pow
-- name    : Formalism.FourierDecayAlt.P.G6.sum_mul_zero_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:55:29.04667+00:00
-- url     : https://prove2.me/theorems/bb08ca1c-d4a0-4726-90eb-31e5b6ef1507
-- title:
--   G6: sum mul zero pow
-- statement:
--   The G6 construction uses the sum mul zero pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RemainderNormLeStrictUpper.lean#L102-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RemainderNormLeStrictUpper.lean#L102-L107

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

theorem Formalism.FourierDecayAlt.P.G6.sum_mul_zero_pow (m : ℕ) (f : ℕ → ℂ) :
    ∑ j ∈ Finset.range (m + 1), f j * (0 : ℂ) ^ (m - j) = f m := by sorry
