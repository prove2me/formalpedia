-- Prove2me | Theorems.Thm_FiniteMagmaE677_four_le_card_class_of_congruence_q_ne
-- name    : FiniteMagmaE677.four_le_card_class_of_congruence_q_ne
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-10-21T04:47:03.372414+00:00
-- url     : https://prove2.me/theorems/e14a225d-3c04-4f33-90a2-31df757224b3
-- title:
--   Counterexample structure (f) — A congruence class that relates a failing point z to q(z) has at least 4 elements
-- statement:
--   Let $(M,\diamond)$ be a finite magma that satisfies E677 and let $\theta$ be a congruence of $(M,\diamond)$. Let $z\in M$ satisfy $((z\diamond z)\diamond z)\diamond z\ne z$, so E255 fails at $z$, and $((z\diamond z)\diamond z)\diamond z\;\theta\;z$. Then the $\theta$-class of $z$ has at least 4 elements. No minimality of $M$ and no property of the quotient beyond this one relation is assumed.
--
--   For a counterexample search: all classes of $\theta$ have the same size, so a congruence that relates a failing point $z$ to $((z\diamond z)\diamond z)\diamond z$ has classes of at least 4 elements.
--
--   Known ingredients. All classes of $\theta$ have the same size: M. Bonatto and D. Stanovský, *Commutator theory for racks and quandles*, arXiv:1902.08980v3, section "Congruences and homomorphisms" (a congruence of a left quasigroup with a connected quotient is uniform). Classes of size 2 give an element $y$ with $y\diamond z=z$ (a short derivation from ETP blueprint Lemma 13.4). Classes of size 3 give such an element by the local form of the argument of Counterexample structure (a). Such an element gives E255 at $z$ (ETP blueprint Lemma 13.2). The bound 4 without minimality was not found in the sources searched: the ETP blueprint, the ETP paper (arXiv:2512.07087v2), the ETP Zulip thread up to 2026-10-14, and papers on left quasigroups and racks.
-- source:
--   Adam McKenna, private repo, 2026-10-20: Lean theorem E677Crit.four_le_card_class_of_q_ne (lean/E677/FixerBlock.lean)

import Definitions.Def_FiniteMagmaE677
import Mathlib

universe u
open FiniteMagmaE677

theorem FiniteMagmaE677.four_le_card_class_of_congruence_q_ne
{α : Type u} [Finite α] (op : α → α → α) (h : FiniteMagmaE677.E677 op)
(r : α → α → Prop) (hr : Equivalence r)
(hcompat : ∀ a a' b b' : α, r a a' → r b b' → r (op a b) (op a' b'))
(z : α) (hz : op (op (op z z) z) z ≠ z)
(hrz : r (op (op (op z z) z) z) z) :
4 ≤ Nat.card {x : α // r z x} := by sorry
