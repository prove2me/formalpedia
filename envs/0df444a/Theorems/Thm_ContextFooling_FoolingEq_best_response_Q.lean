-- Prove2me | Theorems.Thm_ContextFooling_FoolingEq_best_response_Q
-- name    : ContextFooling.FoolingEq.best_response_Q
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:48:41.148803+00:00
-- url     : https://prove2.me/theorems/3a7c715b-99cc-432d-a605-0f45e5e84041
-- title:
--   Proof of Prop. 2, p. 43 (PDF 44) — under θ^k = Q the unique best response is t = (q^Q, p̄_t(q^Q)), a = (q̲, q̲ − ū)
-- statement:
--   Under the standing assumptions, fix an optimistic type $\tilde\beta^0\in(1,\beta)$ and an outside surplus $\bar u\ge0$. As in the proof, there is no maximum price. Consider pairs $(a,t)$ that satisfy all of the following:
--   1. both products are quality-inflated ($\theta_a=\theta_t=Q$);
--   2. $q_a,q_t\ge\underline q$;
--   3. the pair fools $\tilde\beta^0$;
--   4. the type enters, $u_a\ge\bar u$.
--
--   Every such pair earns a margin
--
--   $$p_t-c(q_t)\ \le\ \beta q^Q-c(q^Q)-(\beta-1)\underline q-\bar u.$$
--
--   Equality holds exactly for
--
--   $$t=\bigl(q^Q,\ \beta(q^Q-\underline q)+\underline q-\bar u\bigr),\qquad a=(\underline q,\ \underline q-\bar u).$$
--
--   This pair fools $\tilde\beta^0$, gives $u_a=\bar u$, and attains the bound.
--
--   So a quality-inflating store attracts with the lowest acceptable quality and competes on its price; the best response is unique.
--
--   **Formalization Note.** The statement is at the level of the attraction–target pair. The proof's "$b\to\infty$" is kept: prices are not capped here.
-- source:
--   Apffelstaedt & Mechtenberg, Competition for Context-Sensitive Consumers, MPRA Paper No. 99509 (version of November 2016; published in Management Science, doi:10.1287/mnsc.2020.3675), pp. 42–43 (PDF 43–44), proof of Proposition 2, part a), case θ^k = Q

import Mathlib
import Definitions.Def_ContextFooling_FoolingEq_Model

namespace ContextFooling.FoolingEq

/-- Proof of Proposition 2, p. 43: best response of a store-wide quality-inflating store
(θ^k = Q) to an outside option `ubar` of an optimistic type `β0` (no maximum price, as in the
proof). Every fooling (Q,Q) pair of qualities ≥ q̲ that the type enters earns a margin
p_t − c(q_t) ≤ βq^Q − c(q^Q) − (β − 1)q̲ − ū, attained exactly by t = (q^Q, p̄_t(q^Q)),
a = (q̲, q̲ − ū). -/
theorem best_response_Q (P : Params) (hP : P.Standing) (β0 ubar : ℝ)
    (hβ0 : β0 ∈ Set.Ioo 1 P.β) (hubar : 0 ≤ ubar) :
    (∀ a t : Product, a.θ = Ctx.Q → t.θ = Ctx.Q → Fools P.β β0 a t → P.qlow ≤ a.q →
        P.qlow ≤ t.q → ubar ≤ u a →
        t.p - P.c t.q ≤ P.β * P.qQ - P.c P.qQ - (P.β - 1) * P.qlow - ubar ∧
        (t.p - P.c t.q = P.β * P.qQ - P.c P.qQ - (P.β - 1) * P.qlow - ubar ↔
          t = ⟨P.qQ, P.β * (P.qQ - P.qlow) + P.qlow - ubar, Ctx.Q⟩ ∧
          a = ⟨P.qlow, P.qlow - ubar, Ctx.Q⟩)) ∧
    (Fools P.β β0 ⟨P.qlow, P.qlow - ubar, Ctx.Q⟩
        ⟨P.qQ, P.β * (P.qQ - P.qlow) + P.qlow - ubar, Ctx.Q⟩ ∧
      ubar ≤ u ⟨P.qlow, P.qlow - ubar, Ctx.Q⟩ ∧
      (P.β * (P.qQ - P.qlow) + P.qlow - ubar) - P.c P.qQ =
        P.β * P.qQ - P.c P.qQ - (P.β - 1) * P.qlow - ubar) := by sorry

end ContextFooling.FoolingEq
