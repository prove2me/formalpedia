-- Prove2me | Theorems.Thm_ContextFooling_FoolingEq_cross_regime_deviation
-- name    : ContextFooling.FoolingEq.cross_regime_deviation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:48:47.895419+00:00
-- url     : https://prove2.me/theorems/4e187589-4c05-49d5-b626-5a0943df5c7d
-- title:
--   Proof of Prop. 2, p. 45 (PDF 46) — a deviation to the other store-wide regime is profitable iff ν^(Q,Q) < ν^(P,P) (resp. >)
-- statement:
--   Under the standing assumptions, suppose rivals leave every type the surplus $\bar u=\nu^{(Q,Q)}$. Consider price-inflated pairs $(a,t)$ (both products with context $P$) that satisfy all of the following:
--   1. both products are acceptable;
--   2. the pair fools every type $\tilde\beta\in(1,\beta)$;
--   3. $u_a\ge\nu^{(Q,Q)}$;
--   4. the margin is positive, $p_t-c(q_t)>0$.
--
--   Such a pair exists if and only if
--
--   $$\nu^{(Q,Q)}<\nu^{(P,P)}.$$
--
--   Symmetrically, at $\bar u=\nu^{(P,P)}$ a quality-inflated $(Q,Q)$ pair with the same properties exists if and only if $\nu^{(P,P)}<\nu^{(Q,Q)}$.
--
--   This comparison selects the regime of the store-wide equilibrium in Proposition 2.
--
--   **Formalization Note.** The proof writes the deviation condition as "$q_t-p_t>0$". That is a slip for the deviation's profit $p_t-c(q_t)>0$, which is what is stated here; the conclusion is unchanged.
-- source:
--   Apffelstaedt & Mechtenberg, Competition for Context-Sensitive Consumers, MPRA Paper No. 99509 (version of November 2016; published in Management Science, doi:10.1287/mnsc.2020.3675), p. 45 (PDF 46), proof of Proposition 2, part a)

import Mathlib
import Definitions.Def_ContextFooling_FoolingEq_Model

namespace ContextFooling.FoolingEq

/-- Proof of Proposition 2, p. 45: the deviation to the other store-wide regime. When rivals
leave every type the surplus ν^(Q,Q), some acceptable price-inflating (P,P) pair that fools every
type β̃ ∈ (1, β) and that the types enter earns a positive margin iff ν^(Q,Q) < ν^(P,P); and
symmetrically for a (Q,Q) pair against ν^(P,P). -/
theorem cross_regime_deviation (P : Params) (hP : P.Standing) :
    ((∃ a t : Product, a.θ = Ctx.P ∧ t.θ = Ctx.P ∧ Acceptable P a ∧ Acceptable P t ∧
        (∀ γ ∈ Set.Ioo 1 P.β, Fools P.β γ a t) ∧ nuQQ P ≤ u a ∧ 0 < t.p - P.c t.q) ↔
      nuQQ P < nuPP P) ∧
    ((∃ a t : Product, a.θ = Ctx.Q ∧ t.θ = Ctx.Q ∧ Acceptable P a ∧ Acceptable P t ∧
        (∀ γ ∈ Set.Ioo 1 P.β, Fools P.β γ a t) ∧ nuPP P ≤ u a ∧ 0 < t.p - P.c t.q) ↔
      nuPP P < nuQQ P) := by sorry

end ContextFooling.FoolingEq
