-- Prove2me | Theorems.Thm_FiniteMagmaE677_forty_le_card_of_minimal_counterexample_of_no_idempotent_class
-- name    : FiniteMagmaE677.forty_le_card_of_minimal_counterexample_of_no_idempotent_class
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-10-22T05:42:45.529649+00:00
-- url     : https://prove2.me/theorems/41a7fe43-ca58-4aa1-92ec-afd7ef2f00c7
-- title:
--   Counterexample structure (j) — If the quotient by a non-universal congruence relating z and q(z) has no idempotent, a minimum counterexample has at least 40 elements (conditional on small-order facts)
-- statement:
--   Let $(M,\diamond)$, $z$ and $\theta$ be as in Counterexample structure (h): $M$ is a finite E677 magma of minimum order that fails E255 at $z$, and $\theta$ is a congruence of $(M,\diamond)$ that relates $z$ and $((z\diamond z)\diamond z)\diamond z$ and is not the universal relation. Suppose that no $e\in M$ satisfies $(e\diamond e)\;\theta\;e$, that is, $M/\theta$ has no idempotent. Suppose also these finite facts: no E677 magma has order 6, and every E677 magma of order 7, 8 or 9 has an idempotent. Then $|M|\ge 40$.
--
--   The finite facts are hypotheses of the theorem and are not proved on this platform. For a counterexample search: The proof of Counterexample structure (h) excludes classes of 4 elements (with the order-4 fact) only when $M/\theta$ has an idempotent. So, with the facts of (h) and of this theorem, classes of 4 elements need $|M|\ge 40$; this combines this theorem with that step of the proof of (h) and is not a separate formal statement.
--
--   The finite facts for orders 6, 7 and 8 are described in Counterexample structure (h). Order 9: the only E677 magma of order 9 is the linear one, which has an idempotent (J. Brox, ETP Zulip thread "FINITE: 677 -> 255", 2025-01-10; no certificate). The captain's SAT check, described in (h), also covers order 9. Proof: by the argument of Counterexample structure (b), $|M|=|M/\theta|\cdot m$ with $|M/\theta|\ge 6$ and $m\ge 4$, where $m$ is the size of the $\theta$-classes, and the finite facts give $|M/\theta|\ge 10$. This bound was not found in the sources searched: the ETP blueprint, the ETP paper (arXiv:2512.07087v2) and the ETP Zulip thread up to 2026-10-14.
-- source:
--   Adam McKenna, private repo, 2026-10-21: Lean theorem E677Crit.forty_le_card_of_forall_not_idempotent (lean/E677/MonolithOrderBound.lean; stated there for the least congruence that relates z and q(z), and here for every such congruence)

import Definitions.Def_FiniteMagmaE677
import Mathlib

universe u
open FiniteMagmaE677

theorem FiniteMagmaE677.forty_le_card_of_minimal_counterexample_of_no_idempotent_class
{α : Type u} [Finite α] (op : α → α → α) (h : FiniteMagmaE677.E677 op)
(hmin : ∀ n : ℕ, n < Nat.card α → ∀ op' : Fin n → Fin n → Fin n,
  FiniteMagmaE677.E677 op' → FiniteMagmaE677.E255 op')
(z : α) (hz : op (op (op z z) z) z ≠ z)
(r : α → α → Prop) (hr : Equivalence r)
(hcompat : ∀ a a' b b' : α, r a a' → r b b' → r (op a b) (op a' b'))
(hrz : r z (op (op (op z z) z) z))
(hproper : ∃ a b : α, ¬ r a b)
(hI : ∀ e : α, ¬ r (op e e) e)
(h6 : ∀ op' : Fin 6 → Fin 6 → Fin 6, ¬ FiniteMagmaE677.E677 op')
(h7 : ∀ op' : Fin 7 → Fin 7 → Fin 7, FiniteMagmaE677.E677 op' → ∃ x : Fin 7, op' x x = x)
(h8 : ∀ op' : Fin 8 → Fin 8 → Fin 8, FiniteMagmaE677.E677 op' → ∃ x : Fin 8, op' x x = x)
(h9 : ∀ op' : Fin 9 → Fin 9 → Fin 9, FiniteMagmaE677.E677 op' → ∃ x : Fin 9, op' x x = x) :
40 ≤ Nat.card α := by sorry
