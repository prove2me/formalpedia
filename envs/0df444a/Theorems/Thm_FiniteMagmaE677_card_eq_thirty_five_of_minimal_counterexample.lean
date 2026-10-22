-- Prove2me | Theorems.Thm_FiniteMagmaE677_card_eq_thirty_five_of_minimal_counterexample
-- name    : FiniteMagmaE677.card_eq_thirty_five_of_minimal_counterexample
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-10-22T05:40:48.409049+00:00
-- url     : https://prove2.me/theorems/6c212a9e-6afc-48d6-acfc-13be19d8fbfb
-- title:
--   Counterexample structure (i) — Order 35 with a non-universal congruence relating z and q(z): 7 classes, the class of z has 5 elements, one class idempotent (conditional on an order-7 fact)
-- statement:
--   Let $(M,\diamond)$, $z$ and $\theta$ be as in Counterexample structure (h): $M$ is a finite E677 magma of minimum order that fails E255 at $z$, and $\theta$ is a congruence of $(M,\diamond)$ that relates $z$ and $((z\diamond z)\diamond z)\diamond z$ and is not the universal relation. Suppose also that every E677 magma of order 7 has an idempotent. If $|M|=35$, then $M/\theta$ has 7 elements, the $\theta$-class of $z$ has 5 elements, and some $e\in M$ satisfies $(e\diamond e)\;\theta\;e$, that is, the class of $e$ is an idempotent of $M/\theta$.
--
--   The order-7 fact is a hypothesis of the theorem and is not proved on this platform; it is the only finite fact that the theorem uses. For a counterexample search: a minimum counterexample of order 35 with such a congruence is an extension with classes of 5 elements over an E677 magma of order 7 with an idempotent. By the classification of J. Brox (ETP Zulip thread "FINITE: 677 -> 255", 2025-03-26, no certificate), such a quotient is isomorphic to $x\diamond y=4x+3y$ or to $x\diamond y=4x+y$ on $\mathbb{F}_7$; the captain checked that Brox's two tables are isomorphic to these two operations, one each. This theorem excludes neither one.
--
--   The order-7 fact: J. Brox gave the two isomorphism classes (same thread, 2025-03-26), and both have the idempotent 0 (checked by the captain); B. Reinke (same thread, 2026-05-15) reports that all models of order 7 are linear; the captain's SAT check is described in Counterexample structure (h). Proof: by the argument of Counterexample structure (b), $|M|=|M/\theta|\cdot m$ with $|M/\theta|\ge 6$ and $m\ge 4$, where $m$ is the size of the $\theta$-classes; the only such factorization of 35 is $7\cdot 5$. This statement was not found in the sources searched: the ETP blueprint, the ETP paper (arXiv:2512.07087v2) and the ETP Zulip thread up to 2026-10-14.
-- source:
--   Adam McKenna, private repo, 2026-10-21: Lean theorem E677Crit.card_eq_thirtyFive_of_allE255Below (lean/E677/MonolithOrderBound.lean; stated there for the least congruence that relates z and q(z), and here for every such congruence)

import Definitions.Def_FiniteMagmaE677
import Mathlib

universe u
open FiniteMagmaE677

theorem FiniteMagmaE677.card_eq_thirty_five_of_minimal_counterexample
{α : Type u} [Finite α] (op : α → α → α) (h : FiniteMagmaE677.E677 op)
(hmin : ∀ n : ℕ, n < Nat.card α → ∀ op' : Fin n → Fin n → Fin n,
  FiniteMagmaE677.E677 op' → FiniteMagmaE677.E255 op')
(z : α) (hz : op (op (op z z) z) z ≠ z)
(r : α → α → Prop) (hr : Equivalence r)
(hcompat : ∀ a a' b b' : α, r a a' → r b b' → r (op a b) (op a' b'))
(hrz : r z (op (op (op z z) z) z))
(hproper : ∃ a b : α, ¬ r a b)
(h7 : ∀ op' : Fin 7 → Fin 7 → Fin 7, FiniteMagmaE677.E677 op' → ∃ x : Fin 7, op' x x = x)
(h35 : Nat.card α = 35) :
Nat.card (Quot r) = 7 ∧ Nat.card {x : α // r z x} = 5 ∧ ∃ e : α, r (op e e) e := by sorry
