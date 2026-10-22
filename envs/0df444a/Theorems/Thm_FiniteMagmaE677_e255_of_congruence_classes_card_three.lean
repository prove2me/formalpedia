-- Prove2me | Theorems.Thm_FiniteMagmaE677_e255_of_congruence_classes_card_three
-- name    : FiniteMagmaE677.e255_of_congruence_classes_card_three
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-10-20T22:42:51.607383+00:00
-- url     : https://prove2.me/theorems/951a1653-cc63-444b-811c-4cd78ef31150
-- title:
--   Counterexample structure (a) — Three-element congruence classes lift E255
-- statement:
--   Let $\diamond$ be an operation on a finite set $M$ that satisfies E677, $x=y\diamond(x\diamond((y\diamond x)\diamond y))$. Let $\theta$ be a congruence of $(M,\diamond)$: a reflexive, symmetric and transitive relation such that $a\,\theta\,a'$ and $b\,\theta\,b'$ give $(a\diamond b)\,\theta\,(a'\diamond b')$. Suppose that every $\theta$-class has exactly three elements and that the quotient satisfies E255, that is, $((x\diamond x)\diamond x)\diamond x\;\theta\;x$ for every $x$. Then $(M,\diamond)$ satisfies E255: $x=((x\diamond x)\diamond x)\diamond x$ for every $x$.
--
--   The quotient by such a congruence is an E677 magma with $|M|/3$ elements, so a finite counterexample of minimum order has no congruence whose classes all have three elements.
--
--   Background. ETP blueprint Lemma 13.4 gives E255 for an E677 magma on $G\times A$ with $(x,s)\diamond(y,t)=(x\diamond y,\alpha_{x,y}s+\beta_{x,y}t+c_{x,y})$, where $G$ satisfies E677 and E255, $A$ is an abelian group, and $\alpha_{x,y},\beta_{x,y}$ are endomorphisms of $A$. Classes of size 2 give this form (a short derivation). B. Reinke (ETP Zulip thread "FINITE: 677 -> 255", 2026-06-11) described the weaker form $(x,s)\diamond(y,t)=(x\diamond y,b_{x,y,s}t+c_{x,y,s})$, in which the dependence on $s$ is arbitrary, as the form that the assumptions of S. Chuks-Onah in that discussion give, and wrote that the argument should still work for it. S. Chuks-Onah replied on the same day that for this form the condition that gives E255 is open. When the classes have three elements and each class is identified with $\mathbb{Z}/3$, the operation has the weaker form, because every permutation of a 3-element set is affine over $\mathbb{Z}/3$. So the statement above gives E255 for every finite E677 magma of the weaker form with $A=\mathbb{Z}/3$ over a base $G$ that satisfies E255. The step for classes of size 3 was not found in the sources searched: the ETP blueprint, the ETP paper (arXiv:2512.07087v2), the ETP Zulip thread up to 2026-10-14, and papers on left quasigroups and racks.
-- source:
--   Adam McKenna, private repo, 2026-10-20: Lean theorem E677Crit.MagmaCon.e255_of_card_class_eq_three (lean/E677/ClassThreeLift.lean)

import Definitions.Def_FiniteMagmaE677
import Mathlib

universe u
open FiniteMagmaE677

theorem FiniteMagmaE677.e255_of_congruence_classes_card_three
{α : Type u} [Finite α] (op : α → α → α) (h : FiniteMagmaE677.E677 op)
(r : α → α → Prop) (hr : Equivalence r)
(hcompat : ∀ a a' b b' : α, r a a' → r b b' → r (op a b) (op a' b'))
(hcard : ∀ a : α, Nat.card {x : α // r a x} = 3)
(hquot : ∀ x : α, r (op (op (op x x) x) x) x) :
FiniteMagmaE677.E255 op := by sorry
