-- Prove2me | Theorems.Thm_Formalism_NuclearRankWeightBounds_P_coeff_prod_one_add
-- name    : Formalism.NuclearRankWeightBounds.P.coeff_prod_one_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:03.655562+00:00
-- url     : https://prove2.me/theorems/8057d07d-2bce-4247-ae86-c4655e3052da
-- title:
--   P: coeff prod one add
-- statement:
--   The P construction uses the coeff prod one add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogSumExpBounds/CharacterSumPhase/DetMulDiagonalMulEqSum.lean#L32-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogSumExpBounds/CharacterSumPhase/DetMulDiagonalMulEqSum.lean#L32-L48

import Definitions.Def_Formalism_LogSumExpBounds_NuclearBound
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_DetMulDiagonalMulEqSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.NuclearRankWeightBounds Formalism.NuclearRankWeightBounds.P
open Matrix Polynomial Finset

theorem Formalism.NuclearRankWeightBounds.P.coeff_prod_one_add {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι] (f : ι → R)
    (J : Finset ι) :
    (∏ j ∈ J, (1 + X * C (f j))).coeff 0 = 1 ∧
    (∏ j ∈ J, (1 + X * C (f j))).coeff 1 = ∑ j ∈ J, f j ∧
    2 * (∏ j ∈ J, (1 + X * C (f j))).coeff 2 = (∑ j ∈ J, f j) ^ 2 - ∑ j ∈ J, f j ^ 2 := by sorry
