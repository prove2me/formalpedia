-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_PermutationFixedPoints_inv_exchange
-- name    : Formalism.CyclotomicNorms.PermutationFixedPoints.inv_exchange
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:55:21.206818+00:00
-- url     : https://prove2.me/theorems/4c9d9a31-e27b-4fee-bb07-5b10b2a4faf5
-- title:
--   Permutation Fixed Points: inv exchange
-- statement:
--   The Permutation Fixed Points construction uses the inv exchange property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/TwoMulNumDerangementsLeFactorial.lean#L58-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/TwoMulNumDerangementsLeFactorial.lean#L58-L66

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

theorem Formalism.CyclotomicNorms.PermutationFixedPoints.inv_exchange {α : Type*} [DecidableEq α] (σ : Equiv.Perm α) (S : Finset α)
    (hS : ∀ z, σ z ∈ S ↔ z ∈ S) (x y : α) (hx : σ x = x) (hy : σ y = y) :
    ∀ z, σ z ∈ insert y (S.erase x) ↔ z ∈ insert y (S.erase x) := by sorry
