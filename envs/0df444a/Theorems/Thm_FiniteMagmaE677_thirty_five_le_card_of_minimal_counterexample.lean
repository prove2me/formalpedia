-- Prove2me | Theorems.Thm_FiniteMagmaE677_thirty_five_le_card_of_minimal_counterexample
-- name    : FiniteMagmaE677.thirty_five_le_card_of_minimal_counterexample
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-10-22T05:32:19.981981+00:00
-- url     : https://prove2.me/theorems/06718ae7-742a-4cdd-aae6-42df8fa22231
-- title:
--   Counterexample structure (h) — A minimum counterexample with a non-universal congruence relating z and q(z) has at least 35 elements (conditional on small-order facts)
-- statement:
--   Let $(M,\diamond)$ be a finite magma that satisfies E677 and fails E255 at $z$, that is, $((z\diamond z)\diamond z)\diamond z\ne z$. Suppose that every E677 operation on $\{0,\dots,n-1\}$ with $n<|M|$ satisfies E255, so $M$ is a counterexample of minimum order. Let $\theta$ be a congruence of $(M,\diamond)$ that relates $z$ and $((z\diamond z)\diamond z)\diamond z$ and is not the universal relation. Suppose also these finite facts: no E677 magma has order 4 or 6, and every E677 magma of order 7 or 8 has an idempotent. Then $|M|\ge 35$.
--
--   The finite facts are hypotheses of the theorem and are not proved on this platform. For a counterexample search: with these facts, a minimum counterexample with fewer than 35 elements has no proper congruence that relates $z$ and $((z\diamond z)\diamond z)\diamond z$. This improves the bound 24 of Counterexample structure (b). Counterexample structure (i) treats the case $|M|=35$, and (j) the case where $M/\theta$ has no idempotent.
--
--   The finite facts are known. No E677 magma has order 4 or 6: I. Tencer, ETP Zulip thread "FINITE: 677 -> 255", 2024-12-07 (orders 2, 3, 4 and 6); J. Hyun gives a Lean proof for order 6 (same thread, 2026-09-30, Order6.lean); S. Chuks-Onah (same thread, 2026-05-01, Z3) also reports no E677 magma of order 2, 3, 4 or 6. Order 7: J. Brox gave the two isomorphism classes (same thread, 2025-03-26), and both have the idempotent 0 (checked by the captain); B. Reinke (same thread, 2026-05-15) reports that all models of order 7 are linear; S. Chuks-Onah (same thread, 2026-05-16) found at least 60 distinct E677 tables of order 7 by SAT enumeration, each with exactly one idempotent, and reports (SAT) that no E677 magma of order 7 has $x\diamond x=x$ for every $x$. Order 8: no E677 magma has order 8 (J. Brox, same thread, 2024-12-07, Mace4), so the hypothesis for order 8 holds. Apart from J. Hyun's Lean proof for order 6, these sources give no certificates. The captain also checked the facts with one SAT encoding; drat-trim accepted a DRAT proof of each UNSAT case (unverified C code, not a kernel-checked proof).
--
--   Known ingredients. The proof is the proof of Counterexample structure (b) with two more steps. Write $m$ for the size of the $\theta$-classes; all classes have the same size (M. Bonatto and D. Stanovský, *Commutator theory for racks and quandles*, arXiv:1902.08980v3). (1) If $(e\diamond e)\;\theta\;e$ for some $e$, the class of $e$ is closed under $\diamond$, so it is an E677 magma with $m$ elements; this is the argument of Bonatto and Stanovský for the block of an idempotent. Then $m\ge 5$ and $|M/\theta|\ge 7$. (2) If no class is idempotent in $M/\theta$, the facts for orders 6, 7 and 8 give $|M/\theta|\ge 9$, and $m\ge 4$. The bound 35 was not found in the sources searched: the ETP blueprint, the ETP paper (arXiv:2512.07087v2) and the ETP Zulip thread up to 2026-10-14.
-- source:
--   Adam McKenna, private repo, 2026-10-21: Lean theorem E677Crit.thirtyFive_le_card_of_allE255Below (lean/E677/MonolithOrderBound.lean; stated there for the least congruence that relates z and q(z), and here for every such congruence)

import Definitions.Def_FiniteMagmaE677
import Mathlib

universe u
open FiniteMagmaE677

theorem FiniteMagmaE677.thirty_five_le_card_of_minimal_counterexample
{α : Type u} [Finite α] (op : α → α → α) (h : FiniteMagmaE677.E677 op)
(hmin : ∀ n : ℕ, n < Nat.card α → ∀ op' : Fin n → Fin n → Fin n,
  FiniteMagmaE677.E677 op' → FiniteMagmaE677.E255 op')
(z : α) (hz : op (op (op z z) z) z ≠ z)
(r : α → α → Prop) (hr : Equivalence r)
(hcompat : ∀ a a' b b' : α, r a a' → r b b' → r (op a b) (op a' b'))
(hrz : r z (op (op (op z z) z) z))
(hproper : ∃ a b : α, ¬ r a b)
(h4 : ∀ op' : Fin 4 → Fin 4 → Fin 4, ¬ FiniteMagmaE677.E677 op')
(h6 : ∀ op' : Fin 6 → Fin 6 → Fin 6, ¬ FiniteMagmaE677.E677 op')
(h7 : ∀ op' : Fin 7 → Fin 7 → Fin 7, FiniteMagmaE677.E677 op' → ∃ x : Fin 7, op' x x = x)
(h8 : ∀ op' : Fin 8 → Fin 8 → Fin 8, FiniteMagmaE677.E677 op' → ∃ x : Fin 8, op' x x = x) :
35 ≤ Nat.card α := by sorry
