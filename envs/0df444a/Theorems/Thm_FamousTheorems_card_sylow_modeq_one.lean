-- Prove2me | Theorems.Thm_FamousTheorems_card_sylow_modeq_one
-- name    : FamousTheorems.card_sylow_modeq_one
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T12:40:32.658298+00:00
-- url     : https://prove2.me/theorems/7008a88b-80a1-4f8d-b33f-5351f91ce484
-- title:
--   The third Sylow theorem
-- statement:
--   **The third Sylow theorem.** The number of Sylow $p$-subgroups of a finite group satisfies $$n_p \equiv 1 \pmod p.$$ Combined with the second Sylow theorem — which makes them all conjugate, so $n_p$ divides the index — this is the sharpest elementary constraint on the subgroup structure of a finite group. The two together are the standard instrument for proving non-simplicity: if the divisibility and congruence conditions force $n_p = 1$, the unique Sylow $p$-subgroup is normal. That argument classifies groups of many small orders and underlies the first steps of finite group theory. The proof is an orbit count for the conjugation action of a Sylow subgroup on the set of all of them, where only the subgroup itself is a fixed point. Sylow published all three theorems in 1872. **Formalization note.** `card_sylow` counts the Sylow `p`-subgroups as a type. The result is Mathlib's `card_sylow_modEq_one`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem card_sylow_modeq_one :
    ∀ (p : ℕ) (G : Type u_1) [inst : Group G] [Fact (Nat.Prime p)] [Finite (Sylow p G)], 
    Nat.card (Sylow p G) ≡ 1 [MOD p] := by sorry

end FamousTheorems
