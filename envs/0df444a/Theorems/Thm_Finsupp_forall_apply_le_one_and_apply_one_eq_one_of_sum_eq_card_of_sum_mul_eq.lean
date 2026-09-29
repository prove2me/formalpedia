-- Prove2me | Theorems.Thm_Finsupp_forall_apply_le_one_and_apply_one_eq_one_of_sum_eq_card_of_sum_mul_eq
-- name    : Finsupp.forall_apply_le_one_and_apply_one_eq_one_of_sum_eq_card_of_sum_mul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/b529f79d-c5c5-56c5-a50d-13e415ccec29
-- title:
--   Multiplicity-freeness from two character sum identities
-- statement:
--   Let $C$ be a finite commutative group and $K$ a field of characteristic zero. Let $m$ be a finitely supported function from the group $C \to^* K^\times$ of monoid homomorphisms (characters) $C \to K^\times$ to the natural numbers, and let $f \colon C \to K$ be a function such that for every $c \in C$ one has $f(c) = \sum_{\mu} m(\mu)\,\mu(c)$, the sum being the finitely supported sum over the support of $m$, with $m(\mu)$ regarded in $K$ and $\mu(c)$ via the inclusion $K^\times \hookrightarrow K$. Assume the two identities $\sum_{c \in C} f(c) = |C|$ and $\sum_{c \in C} f(c) f(c^{-1}) = \bigl(\sum_{\mu} m(\mu)\bigr)\,|C|$ in $K$, where $|C|$ denotes the cardinality of $C$ cast into $K$. The conclusion is the conjunction: $m(\mu) \le 1$ for every character $\mu$, and $m(\mathbf 1) = 1$ for the trivial character.
--
--   This is the elementary character-theoretic criterion for a virtual character of a finite abelian group, written as a non-negative integral combination $f = \sum_\mu m(\mu)\mu$, to be multiplicity-free and to contain the trivial character exactly once. It is used in the analysis of cuspidal representations restricted to a non-split torus, through [`CuspidalType.exists_sq_ne_one_and_forall_charpoly_torus_mul_eq_prod_of_forall_character_eq`](thm.html#CuspidalType.exists_sq_ne_one_and_forall_charpoly_torus_mul_eq_prod_of_forall_character_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Finsupp_forall_apply_le_one_and_apply_one_eq_one_of_sum_eq_card_of_sum_mul_eq.lean

import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial CuspidalType

theorem Finsupp.forall_apply_le_one_and_apply_one_eq_one_of_sum_eq_card_of_sum_mul_eq {C : Type*} [CommGroup C] [Fintype C] {K : Type*} [Field K] [CharZero K]
    (m : (C →* Kˣ) →₀ ℕ) (f : C → K) (hf : ∀ c, f c = m.sum fun μ n => (n : K) * ((μ c : Kˣ) : K))
    (h1 : ∑ c, f c = Fintype.card C)
    (h2 : ∑ c, f c * f c⁻¹ = (m.sum fun _ n => (n : K)) * Fintype.card C) :
    (∀ μ, m μ ≤ 1) ∧ m 1 = 1 := by sorry
