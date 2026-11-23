-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_PermutationFixedPoints_card_stab_le
-- name    : Formalism.CyclotomicNorms.PermutationFixedPoints.card_stab_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:55:15.053744+00:00
-- url     : https://prove2.me/theorems/443a3237-884c-4492-bd51-84ef84736fdf
-- title:
--   Permutation Fixed Points: card stab le
-- statement:
--   The Permutation Fixed Points construction uses the card stab le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/TwoMulNumDerangementsLeFactorial.lean#L95-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/TwoMulNumDerangementsLeFactorial.lean#L95-L117

import Definitions.Def_Formalism_CyclotomicNorms_DiscardKernel
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_TwoMulNumDerangementsLeFactorial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.CyclotomicNorms Formalism.CyclotomicNorms.PermutationFixedPoints

theorem Formalism.CyclotomicNorms.PermutationFixedPoints.card_stab_le (N : ℕ) (S : Finset (Fin N)) :
    (univ.filter (fun σ : Equiv.Perm (Fin N) => ∀ x, σ x ∈ S ↔ x ∈ S)).card ≤
      S.card.factorial * (N - S.card).factorial := by sorry
