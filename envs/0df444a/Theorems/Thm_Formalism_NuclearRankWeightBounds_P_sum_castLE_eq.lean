-- Prove2me | Theorems.Thm_Formalism_NuclearRankWeightBounds_P_sum_castLE_eq
-- name    : Formalism.NuclearRankWeightBounds.P.sum_castLE_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:17:36.208908+00:00
-- url     : https://prove2.me/theorems/43dada5c-055d-43ff-918e-f05c0a77188e
-- title:
--   P: sum cast LE eq
-- statement:
--   The P construction uses the sum cast LE eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogSumExpBounds/CharacterSumPhase/DetMulDiagonalMulEqSum.lean#L112-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogSumExpBounds/CharacterSumPhase/DetMulDiagonalMulEqSum.lean#L112-L115

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

theorem Formalism.NuclearRankWeightBounds.P.sum_castLE_eq {N i : ℕ} (hi : i ≤ N) {β : Type*} [AddCommMonoid β] (f : Fin N → β) :
    ∑ a : Fin i, f (Fin.castLE hi a) = ∑ a ∈ univ.filter (fun a : Fin N => a.val < i), f a := by sorry
