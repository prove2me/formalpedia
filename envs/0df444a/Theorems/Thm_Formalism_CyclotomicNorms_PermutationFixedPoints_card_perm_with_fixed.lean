-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_PermutationFixedPoints_card_perm_with_fixed
-- name    : Formalism.CyclotomicNorms.PermutationFixedPoints.card_perm_with_fixed
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:55:18.165804+00:00
-- url     : https://prove2.me/theorems/dae7ce4e-20b7-4be2-99ad-815d44bc7549
-- title:
--   Permutation Fixed Points: card perm with fixed
-- statement:
--   The Permutation Fixed Points construction uses the card perm with fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/TwoMulNumDerangementsLeFactorial.lean#L32-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/TwoMulNumDerangementsLeFactorial.lean#L32-L46

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

theorem Formalism.CyclotomicNorms.PermutationFixedPoints.card_perm_with_fixed {α : Type*} [Fintype α] [DecidableEq α] (h : 1 ≤ Fintype.card α) :
    (Fintype.card α).factorial ≤
      2 * (univ.filter (fun p : Equiv.Perm α => ∃ x, p x = x)).card := by sorry
