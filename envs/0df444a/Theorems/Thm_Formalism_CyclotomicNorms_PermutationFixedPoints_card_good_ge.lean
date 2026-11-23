-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_PermutationFixedPoints_card_good_ge
-- name    : Formalism.CyclotomicNorms.PermutationFixedPoints.card_good_ge
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:55:13.941794+00:00
-- url     : https://prove2.me/theorems/53dd96ce-a510-43f0-9bef-54108856519b
-- title:
--   Permutation Fixed Points: card good ge
-- statement:
--   The Permutation Fixed Points construction uses the card good ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/TwoMulNumDerangementsLeFactorial.lean#L119-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/TwoMulNumDerangementsLeFactorial.lean#L119-L176

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

theorem Formalism.CyclotomicNorms.PermutationFixedPoints.card_good_ge (N a : ℕ) (ha : 0 < a) (haN : a < N) (S : Finset (Fin N))
    (hS : S.card = a) :
    a.factorial * (N - a).factorial ≤
      4 * (univ.filter (fun σ : Equiv.Perm (Fin N) =>
        (∀ x, σ x ∈ S ↔ x ∈ S) ∧ 2 ≤ numInv N a σ)).card := by sorry
