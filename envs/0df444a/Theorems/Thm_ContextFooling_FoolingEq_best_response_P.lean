-- Prove2me | Theorems.Thm_ContextFooling_FoolingEq_best_response_P
-- name    : ContextFooling.FoolingEq.best_response_P
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:48:43.014521+00:00
-- url     : https://prove2.me/theorems/432180a5-379c-473f-a0bd-3abeab575edb
-- title:
--   Proof of Prop. 2, p. 44 (PDF 45) — under θ^k = P the unique best response is t = (q^P, p̄_t(q^P)), a = (b + ū, b)
-- statement:
--   Under the standing assumptions, fix an optimistic type $\tilde\beta^0\in(1,\beta)$ and an outside surplus $\bar u\ge0$. Consider pairs $(a,t)$ that satisfy all of the following:
--   1. both products are price-inflated ($\theta_a=\theta_t=P$);
--   2. both are acceptable ($q\ge\underline q$, $p\le b$);
--   3. the pair fools $\tilde\beta^0$;
--   4. the type enters, $u_a\ge\bar u$.
--
--   Every such pair earns a margin
--
--   $$p_t-c(q_t)\ \le\ \frac{q^P-\beta c(q^P)+(\beta-1)b-\bar u}{\beta}.$$
--
--   Equality holds exactly for
--
--   $$t=\Bigl(q^P,\ b-\tfrac{b+\bar u-q^P}{\beta}\Bigr),\qquad a=(b+\bar u,\ b).$$
--
--   When $q^P<b+\bar u$, that is, when the target's price is below $b$, this pair is acceptable, fools $\tilde\beta^0$, gives $u_a=\bar u$, and attains the bound.
--
--   So a price-inflating store attracts with the highest acceptable price and competes on the quality of that product.
--
--   **Formalization Note.** The price cap $p\le b$ is kept, because the proof itself sets $p_a=b$. The condition $q^P<b+\bar u$ for the maximizer to be a fooling pair is the proof's "for any $p_t<b$" (p. 44). Without it the maximizer has $p_t\ge p_a$ and does not fool.
-- source:
--   Apffelstaedt & Mechtenberg, Competition for Context-Sensitive Consumers, MPRA Paper No. 99509 (version of November 2016; published in Management Science, doi:10.1287/mnsc.2020.3675), pp. 43–44 (PDF 44–45), proof of Proposition 2, part a), case θ^k = P

import Mathlib
import Definitions.Def_ContextFooling_FoolingEq_Model

namespace ContextFooling.FoolingEq

/-- Proof of Proposition 2, pp. 43–44: best response of a store-wide price-inflating store
(θ^k = P) to an outside option `ubar` of an optimistic type `β0`. Every acceptable fooling
(P,P) pair the type enters earns a margin p_t − c(q_t) ≤ [q^P − βc(q^P) + (β − 1)b − ū]/β,
attained exactly by t = (q^P, p̄_t(q^P)), a = (b + ū, b); the maximizer is a fooling pair
whenever p̄_t(q^P) < b, i.e. q^P < b + ū. -/
theorem best_response_P (P : Params) (hP : P.Standing) (β0 ubar : ℝ)
    (hβ0 : β0 ∈ Set.Ioo 1 P.β) (hubar : 0 ≤ ubar) :
    (∀ a t : Product, a.θ = Ctx.P → t.θ = Ctx.P → Fools P.β β0 a t → Acceptable P a →
        Acceptable P t → ubar ≤ u a →
        t.p - P.c t.q ≤ (P.qP - P.β * P.c P.qP + (P.β - 1) * P.b - ubar) / P.β ∧
        (t.p - P.c t.q = (P.qP - P.β * P.c P.qP + (P.β - 1) * P.b - ubar) / P.β ↔
          t = ⟨P.qP, P.b - (P.b + ubar - P.qP) / P.β, Ctx.P⟩ ∧
          a = ⟨P.b + ubar, P.b, Ctx.P⟩)) ∧
    (P.qP < P.b + ubar →
      Fools P.β β0 ⟨P.b + ubar, P.b, Ctx.P⟩ ⟨P.qP, P.b - (P.b + ubar - P.qP) / P.β, Ctx.P⟩ ∧
      Acceptable P ⟨P.b + ubar, P.b, Ctx.P⟩ ∧
      Acceptable P ⟨P.qP, P.b - (P.b + ubar - P.qP) / P.β, Ctx.P⟩ ∧
      ubar ≤ u ⟨P.b + ubar, P.b, Ctx.P⟩ ∧
      (P.b - (P.b + ubar - P.qP) / P.β) - P.c P.qP =
        (P.qP - P.β * P.c P.qP + (P.β - 1) * P.b - ubar) / P.β) := by sorry

end ContextFooling.FoolingEq
