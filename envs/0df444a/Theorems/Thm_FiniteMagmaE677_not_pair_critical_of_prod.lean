-- Prove2me | Theorems.Thm_FiniteMagmaE677_not_pair_critical_of_prod
-- name    : FiniteMagmaE677.not_pair_critical_of_prod
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-10-22T05:52:04.302165+00:00
-- url     : https://prove2.me/theorems/9b9103a5-3ee0-413e-94c2-c539b32ffae0
-- title:
--   Counterexample structure (l) — In a product of two magmas with at least two elements each, no point where E255 fails has the congruence property 3 of (k)
-- statement:
--   Let $(A,\diamond_1)$ and $(C,\diamond_2)$ be magmas, each with at least two elements, and let $\diamond$ be the componentwise operation on $A\times C$:
--
--   $$(a,c)\diamond(a',c')=(a\diamond_1 a',\;c\diamond_2 c').$$
--
--   Let $z\in A\times C$ with $q(z)\ne z$, where $q(z)=((z\diamond z)\diamond z)\diamond z$. A congruence of $(A\times C,\diamond)$ is a reflexive, symmetric and transitive relation $\theta$ such that $u\,\theta\,u'$ and $v\,\theta\,v'$ give $(u\diamond v)\,\theta\,(u'\diamond v')$. Then it is not true that every congruence of $(A\times C,\diamond)$ that relates two distinct elements relates $z$ and $q(z)$. Neither magma is assumed to be finite or to satisfy E677.
--
--   So property 3 of Counterexample structure (k) fails at each point of such a product at which E255 fails. For a counterexample search: a product of two magmas with at least two elements each has no point with properties 1 and 3 of (k). This applies to the product $\alpha\times K$ of item 1 of the mission description; there $\alpha$ has at least two elements, because $x\diamond x\ne x$. S. Chuks-Onah (ETP Zulip thread "FINITE: 677 -> 255", 2026-06-10) lists, among the known facts about a minimal counterexample $M$: "E255 fails componentwise, so $M$ is not a direct product". The theorem is the case of two factors of the standard fact that a subdirectly irreducible algebra is directly indecomposable (S. Burris and H. P. Sankappanavar, *A Course in Universal Algebra*, Theorem II.8.5), and the proof is the standard one with the kernels of the two projections. It is not a new result.
--
--   **Formalization Note** The product operation is an operation `op` on `α × β` with `op p r = (op₁ p.1 r.1, op₂ p.2 r.2)` for all `p` and `r`; `Nontrivial α` says that `α` has two distinct elements. The conclusion is the negation of property 3 of (k) at `z`, written in the same form. The theorem is about the product type itself; a magma that is only isomorphic to a product needs a transport step that is not part of this statement.
-- source:
--   Adam McKenna, private repo, 2026-08-03: Lean theorem E677Crit.not_pairCritical_prod_of_q_ne (lean/E677/CriticalCore.lean)

import Definitions.Def_FiniteMagmaE677
import Mathlib

universe u v
open FiniteMagmaE677

theorem FiniteMagmaE677.not_pair_critical_of_prod
{α : Type u} {β : Type v} [Nontrivial α] [Nontrivial β]
(op₁ : α → α → α) (op₂ : β → β → β) (op : α × β → α × β → α × β)
(hop : ∀ p r : α × β, op p r = (op₁ p.1 r.1, op₂ p.2 r.2))
(z : α × β) (hz : op (op (op z z) z) z ≠ z) :
¬ ∀ r : α × β → α × β → Prop, Equivalence r →
  (∀ a a' b b' : α × β, r a a' → r b b' → r (op a b) (op a' b')) →
  ∀ a b : α × β, a ≠ b → r a b → r z (op (op (op z z) z) z) := by sorry
