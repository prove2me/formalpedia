-- Prove2me | Theorems.Thm_ContextFooling_FoolingEq_best_response_product_specific
-- name    : ContextFooling.FoolingEq.best_response_product_specific
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:48:51.652468+00:00
-- url     : https://prove2.me/theorems/06a46f06-dbbd-4eb7-b582-6de8d92f854f
-- title:
--   Proof of Prop. 2, p. 46 (PDF 47) — with product-specific contexts the unique best response is Θ^k = (P, Q), t = (q^Q, p̄_t(q^Q)), a = (b + ū, b)
-- statement:
--   Under the standing assumptions, fix an optimistic type $\tilde\beta^0\in(1,\beta)$ and an outside surplus $\bar u$ in the domain of positive profits, $0\le\bar u\le\nu^{(P,Q)}$, where $\nu^{(P,Q)}=\beta q^Q-c(q^Q)+(\beta-1)b$. Consider pairs $(a,t)$ with arbitrary contexts that satisfy all of the following:
--   1. both products are acceptable;
--   2. the pair fools $\tilde\beta^0$;
--   3. the type enters, $u_a\ge\bar u$.
--
--   Every such pair earns a margin
--
--   $$p_t-c(q_t)\ \le\ \nu^{(P,Q)}-\bar u.$$
--
--   Equality holds exactly for $(\theta_a,\theta_t)=(P,Q)$ with
--
--   $$t=\bigl(q^Q,\ \beta q^Q-\bar u+(\beta-1)b\bigr),\qquad a=(b+\bar u,\ b).$$
--
--   When both products of this pair are acceptable, it fools $\tilde\beta^0$, gives $u_a=\bar u$, and attains the bound.
--
--   So with product-specific contexts the store inflates the price of the attraction product and the quality of the target.
--
--   **Formalization Note.** The restriction $\bar u\le\nu^{(P,Q)}$ is the proof's "domain of positive profits". Without it, for large $\bar u$, a $(P,P)$ pair's bound $(\nu^{(P,P)}-\bar u)/\beta$ exceeds $\nu^{(P,Q)}-\bar u$. Prices are capped at $b$, because the proof sets $p_a=b$. The maximizer's acceptability is a hypothesis of the attainment clause, since with the cap it can fail for small $\bar u$. The proof's step comparing $(P,Q)$ with $(Q,Q)$ at $q_a=\underline q$ is not used; only the comparison of the bounds is stated.
-- source:
--   Apffelstaedt & Mechtenberg, Competition for Context-Sensitive Consumers, MPRA Paper No. 99509 (version of November 2016; published in Management Science, doi:10.1287/mnsc.2020.3675), pp. 45–46 (PDF 46–47), proof of Proposition 2, part b)

import Mathlib
import Definitions.Def_ContextFooling_FoolingEq_Model

namespace ContextFooling.FoolingEq

/-- Proof of Proposition 2, pp. 45–46: best response with product-specific contexts, for an
outside option `ubar` of an optimistic type `β0` in the domain of positive profits
0 ≤ ū ≤ ν^(P,Q). Every acceptable fooling pair, with any contexts, that the type enters earns a
margin ≤ ν^(P,Q) − ū, with equality exactly for (θ_a, θ_t) = (P, Q), t = (q^Q, p̄_t(q^Q)),
a = (b + ū, b); this maximizer fools whenever both of its products are acceptable. -/
theorem best_response_product_specific (P : Params) (hP : P.Standing) (β0 ubar : ℝ)
    (hβ0 : β0 ∈ Set.Ioo 1 P.β) (hubar : 0 ≤ ubar) (hdom : ubar ≤ nuPQ P) :
    (∀ a t : Product, Fools P.β β0 a t → Acceptable P a → Acceptable P t → ubar ≤ u a →
        t.p - P.c t.q ≤ nuPQ P - ubar ∧
        (t.p - P.c t.q = nuPQ P - ubar ↔
          t = ⟨P.qQ, P.β * P.qQ - ubar + (P.β - 1) * P.b, Ctx.Q⟩ ∧
          a = ⟨P.b + ubar, P.b, Ctx.P⟩)) ∧
    (Acceptable P ⟨P.b + ubar, P.b, Ctx.P⟩ →
      Acceptable P ⟨P.qQ, P.β * P.qQ - ubar + (P.β - 1) * P.b, Ctx.Q⟩ →
      Fools P.β β0 ⟨P.b + ubar, P.b, Ctx.P⟩ ⟨P.qQ, P.β * P.qQ - ubar + (P.β - 1) * P.b, Ctx.Q⟩ ∧
      ubar ≤ u ⟨P.b + ubar, P.b, Ctx.P⟩ ∧
      (P.β * P.qQ - ubar + (P.β - 1) * P.b) - P.c P.qQ = nuPQ P - ubar) := by sorry

end ContextFooling.FoolingEq
