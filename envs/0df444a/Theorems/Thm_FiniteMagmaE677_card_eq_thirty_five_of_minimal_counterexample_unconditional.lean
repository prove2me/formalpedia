-- Prove2me | Theorems.Thm_FiniteMagmaE677_card_eq_thirty_five_of_minimal_counterexample_unconditional
-- name    : FiniteMagmaE677.card_eq_thirty_five_of_minimal_counterexample_unconditional
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-10-30T17:33:15.935005+00:00
-- url     : https://prove2.me/theorems/666937e2-bfee-4d7b-87a5-347b2a213061
-- title:
--   Counterexample structure (i) — Order 35 with a non-universal congruence relating z and q(z): 7 classes, the class of z has 5 elements, one class idempotent (no small-order hypothesis)
-- statement:
--   Let $(M,\diamond)$, $z$ and $\theta$ be as in Counterexample structure (h): $M$ is a finite E677 magma of minimum order that fails E255 at $z$, and $\theta$ is a congruence of $(M,\diamond)$ that relates $z$ and $((z\diamond z)\diamond z)\diamond z$ and is not the universal relation. If $|M|=35$, then $M/\theta$ has 7 elements, the $\theta$-class of $z$ has 5 elements, and some $e\in M$ satisfies $(e\diamond e)\;\theta\;e$, that is, the class of $e$ is an idempotent of $M/\theta$.
--
--   This is the statement of Counterexample structure (i) without its hypothesis h7 (every E677 magma of order 7 has an idempotent). The theorem has no small-order hypothesis: Small orders (7) proves h7.
--
--   For a counterexample search: a minimum counterexample of order 35 with such a congruence is an extension with classes of 5 elements over an E677 magma of order 7 with an idempotent. J. Brox (ETP Zulip thread "FINITE: 677 -> 255", 2025-03-26, no certificate) gave the two isomorphism classes of E677 magmas of order 7; the captain checked that Brox's two tables are isomorphic to $x\diamond y=4x+y$ and $x\diamond y=4x+3y$ on $\mathbb{F}_7$, one each. This theorem excludes neither one.
--
--   We did not find a proof of this statement in the ETP blueprint, the ETP paper (arXiv:2512.07087v2) or the ETP Zulip thread up to 2026-10-14. Credit for the order-7 fact: see Small orders (7).
-- source:
--   Adam McKenna, private repo, 2026-10-27: reduction of Counterexample structure (i) (FiniteMagmaE677.card_eq_thirty_five_of_minimal_counterexample) and Small orders (7) (FiniteMagmaE677.exists_idempotent_of_card_seven), both Proved on this platform

import Definitions.Def_FiniteMagmaE677
import Mathlib

universe u
open FiniteMagmaE677

theorem FiniteMagmaE677.card_eq_thirty_five_of_minimal_counterexample_unconditional
{α : Type u} [Finite α] (op : α → α → α) (h : FiniteMagmaE677.E677 op)
(hmin : ∀ n : ℕ, n < Nat.card α → ∀ op' : Fin n → Fin n → Fin n,
  FiniteMagmaE677.E677 op' → FiniteMagmaE677.E255 op')
(z : α) (hz : op (op (op z z) z) z ≠ z)
(r : α → α → Prop) (hr : Equivalence r)
(hcompat : ∀ a a' b b' : α, r a a' → r b b' → r (op a b) (op a' b'))
(hrz : r z (op (op (op z z) z) z))
(hproper : ∃ a b : α, ¬ r a b)
(h35 : Nat.card α = 35) :
Nat.card (Quot r) = 7 ∧ Nat.card {x : α // r z x} = 5 ∧ ∃ e : α, r (op e e) e := by sorry
