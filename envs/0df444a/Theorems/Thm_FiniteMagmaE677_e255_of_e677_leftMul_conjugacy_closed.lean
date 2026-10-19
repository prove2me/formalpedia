-- Prove2me | Theorems.Thm_FiniteMagmaE677_e255_of_e677_leftMul_conjugacy_closed
-- name    : FiniteMagmaE677.e255_of_e677_leftMul_conjugacy_closed
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-10-13T16:58:35.963289+00:00
-- url     : https://prove2.me/theorems/4d77dac7-2852-4dc1-b5e0-846fb6245b58
-- title:
--   Conditional E255: left translations closed under conjugation (Padilla)
-- statement:
--   This is a conditional implication announced by J Ignacio Padilla on 2026-10-10 in the Lean Zulip topic "FINITE: 677 -> 255", with a Lean proof file in pull request #1518 of the Equational Theories Project (closed without merge by its author on 2026-10-13). Proved on this platform on 2026-10-14 (UTC) by omegaestable; the accepted proof uses a different argument from the pull request. The extra hypothesis is a closure condition on left translations. It is not known to follow from E677, and the theorem does not resolve the unrestricted finite implication E677 $\to$ E255.
--
--   Let $(\alpha,\diamond)$ be a finite magma satisfying E677: for all $p,q\in\alpha$,
--   $$p = q\diamond\bigl(p\diamond((q\diamond p)\diamond q)\bigr).$$
--   For $a\in\alpha$ write $L_a(z)=a\diamond z$ for left translation by $a$. In a finite E677 magma every $L_a$ is a bijection. Assume that the left translations are closed under conjugation by left translations: for all $a,b\in\alpha$ there is $c\in\alpha$ with
--   $$L_c\circ L_a = L_a\circ L_b,\qquad\text{that is,}\qquad L_c = L_a\circ L_b\circ L_a^{-1}.$$
--   Then $\alpha$ satisfies E255: for every $x\in\alpha$,
--   $$x = ((x\diamond x)\diamond x)\diamond x.$$
--
--   The hypothesis holds in every affine model $x\diamond y = \lambda x+\mu y$ over $\mathbb{Z}/m$ that satisfies E677. A computational check against the community database of finite E677 magmas at https://eq677.icarm.cloud (4091 tables as of 2026-09-27) found the hypothesis true in $875$ of them and false in $3216$, with order $21$ the smallest failing order; every one of those magmas satisfies E255. So the theorem settles the finite implication on a proper subclass only. Its role on the mission is as one case of a possible case split, not as a route to the main theorem.
--
--   **Formalization Note** The source states the hypothesis with an inverse, $L_c = L_a\circ L_b\circ L_a^{-1}$, with $L_a$ packaged as a bijection. Here it is stated without inverses, as $c\diamond(a\diamond z) = a\diamond(b\diamond z)$ for all $z$. Because $L_a$ is a bijection in a finite E677 magma, the source form implies this form (instantiate the source at $z = a\diamond w$ and use $L_a^{-1}(a\diamond w) = w$), and this form implies the source form (instantiate this form at $w = L_a^{-1}(z)$ and use $a\diamond L_a^{-1}(z) = z$). Finiteness is carried by `Fintype α`. The empty magma satisfies E255 vacuously, so no nonemptiness hypothesis is needed.
-- source:
--   J Ignacio Padilla, theorem `Eq677.eq255_of_eq677_leftMul_conjugacy_closed`, Equational Theories Project pull request #1518 (https://github.com/teorth/equational_theories/pull/1518), head commit a1e424c5738b28b2411622779ddefead0e760767, file equational_theories/ManuallyProved/Equation677.lean, lines 283-291; discussion in issue #1517 (https://github.com/teorth/equational_theories/issues/1517); announced 2026-10-10 in Lean Zulip channel Equational, topic "FINITE: 677 -> 255" (https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/FINITE.3A.20677.20-.3E.20255).

import Definitions.Def_FiniteMagmaE677
import Mathlib

universe u
open FiniteMagmaE677

theorem FiniteMagmaE677.e255_of_e677_leftMul_conjugacy_closed
{α : Type u} [Fintype α] (op : α → α → α) (h : FiniteMagmaE677.E677 op)
(hconj : ∀ a b : α, ∃ c : α, ∀ z : α, op c (op a z) = op a (op b z)) :
FiniteMagmaE677.E255 op := by sorry
