-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_count2
-- name    : Formalism.LogVandermondeBounds.product_first_zeroth_parts.count2
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T09:52:59.749159+00:00
-- url     : https://prove2.me/theorems/2d09e21c-1967-4972-b4d7-f767c8d7d22c
-- title:
--   product first zeroth parts: count2
-- statement:
--   The product first zeroth parts construction uses the count2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/RamifiedLatticeOperatorIdentity.lean#L192-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/RamifiedLatticeOperatorIdentity.lean#L192-L226

import Definitions.Def_Formalism_LogVandermondeBounds_FinrankFiberSumZero
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_RamifiedLatticeOperatorIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.product_first_zeroth_parts
open Finset
variable {k : Type*} [Field k] [Fintype k] [DecidableEq k] {r : ℕ} {R : Type*} [CommRing R]

theorem Formalism.LogVandermondeBounds.product_first_zeroth_parts.count2 (hr : 2 ≤ r) {x y : Fin r → k} (hx : x ≠ 0) (hy : ∀ c : k, y ≠ c • x) (a b : k) :
    (univ.filter (fun f : Fin r → k => pair f x = a ∧ pair f y = b)).card =
      Fintype.card k ^ (r - 2) := by sorry
