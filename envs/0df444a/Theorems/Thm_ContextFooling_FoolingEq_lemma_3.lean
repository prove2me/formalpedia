-- Prove2me | Theorems.Thm_ContextFooling_FoolingEq_lemma_3
-- name    : ContextFooling.FoolingEq.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:48:46.219979+00:00
-- url     : https://prove2.me/theorems/67c074bc-0557-43f2-976d-ea1cd7f53926
-- title:
--   Lemma 3, p. 13 (PDF 14) — fooling pessimists is unprofitable; fooling optimists is profitable with (Q,Q) up-selling, (P,P) down-selling, or (P,Q), (P,N), (N,Q)
-- statement:
--   Let $\beta>1$, let $\underline q>0$ be the minimum quality, and let there be no maximum price (the lemma's "$b\to\infty$"). Fix a type $\tilde\beta^0>1$ and an outside surplus $\bar u\ge0$. Fix a target quality $q_t\ge\underline q$, and let $p^0_t:=q_t-\bar u$ be the highest price at which $q_t$ sells without fooling. An attraction product $a$ is admissible when $q_a\ge\underline q$ and $u_a\ge\bar u$. Then:
--
--   1. **Pessimists.** If $\tilde\beta^0>\beta$, every pair $(a,t)$ with $q_t$ given that fools $\tilde\beta^0$, with admissible $a$, has $p_t<p^0_t$.
--   2. **Optimists.** If $\tilde\beta^0<\beta$, there is a pair $(a,t)$ with target quality $q_t$ and admissible $a$ that fools $\tilde\beta^0$ and sells at $p_t>p^0_t$, in each of the following cases:
--      - $(\theta_a,\theta_t)=(Q,Q)$ with $q_a<q_t$ (provided $q_t>\underline q$);
--      - $(\theta_a,\theta_t)=(P,P)$ with $p_t<p_a$;
--      - $(\theta_a,\theta_t)\in\{(P,Q),(P,N),(N,Q)\}$.
--   3. **Other contexts (optimists).** Every $(Q,Q)$ pair that fools $\tilde\beta^0$ up-sells ($q_a<q_t$, $p_a<p_t$). Every $(P,P)$ pair that fools her down-sells ($q_t<q_a$, $p_t<p_a$). No pair with $(\theta_a,\theta_t)\in\{(Q,P),(Q,N),(N,P)\}$, $q_a\ge\underline q$ and $p_t\ge0$ fools her.
--
--   In short,
--
--   $$\tilde\beta^0>\beta\ \Rightarrow\ p_t<p^0_t,\qquad \tilde\beta^0<\beta\ \Rightarrow\ \exists\,(a,t):\ p_t>p^0_t.$$
--
--   The lemma is the reason the equilibria of Proposition 2 involve fooling and a distorted store context.
--
--   **Formalization Note.** The (Q,Q) bullet is stated for $q_t>\underline q$. At $q_t=\underline q$ there is no acceptable $q_a<q_t$, so the printed statement fails there; the proof assumes $\underline q\to0$ (p. 37). "Fooling with other store-contexts is unprofitable" is rendered by item 3: outside the listed configurations an optimist cannot be fooled at all. The hypothesis $\tilde\beta^0>1$ is the paper's $f=0$ on $\tilde\beta\le1$.
-- source:
--   Apffelstaedt & Mechtenberg, Competition for Context-Sensitive Consumers, MPRA Paper No. 99509 (version of November 2016; published in Management Science, doi:10.1287/mnsc.2020.3675), p. 13 (PDF 14), Lemma 3; proof pp. 37–41 (PDF 38–42)

import Mathlib
import Definitions.Def_ContextFooling_FoolingEq_Model

namespace ContextFooling.FoolingEq

/-- Lemma 3 (Profitable Fooling), p. 13, with no maximum price ("b → ∞"). Here `ubar` is the
outside surplus ū(β̃⁰) ≥ 0 of type `β0`, `qt ≥ q̲` the target quality and `qt - ubar` the
no-fooling price p⁰_t. Products below the minimum quality `qlow` cannot attract. -/
theorem lemma_3 (β β0 qlow ubar qt : ℝ) (hβ : 1 < β) (hβ0 : 1 < β0) (hqlow : 0 < qlow)
    (hubar : 0 ≤ ubar) (hqt : qlow ≤ qt) :
    -- a) fooling a pessimist forces a price strictly below p⁰_t
    (β < β0 → ∀ a t : Product, t.q = qt → Fools β β0 a t → qlow ≤ a.q → ubar ≤ u a →
        t.p < qt - ubar) ∧
    -- b) fooling an optimist is profitable with the listed context pairs
    (β0 < β →
      (qlow < qt → ∃ a t : Product, a.θ = Ctx.Q ∧ t.θ = Ctx.Q ∧ t.q = qt ∧ qlow ≤ a.q ∧
          ubar ≤ u a ∧ Fools β β0 a t ∧ a.q < qt ∧ qt - ubar < t.p) ∧
      (∃ a t : Product, a.θ = Ctx.P ∧ t.θ = Ctx.P ∧ t.q = qt ∧ qlow ≤ a.q ∧
          ubar ≤ u a ∧ Fools β β0 a t ∧ t.p < a.p ∧ qt - ubar < t.p) ∧
      (∀ θa θt : Ctx,
          (θa, θt) = (Ctx.P, Ctx.Q) ∨ (θa, θt) = (Ctx.P, Ctx.N) ∨ (θa, θt) = (Ctx.N, Ctx.Q) →
        ∃ a t : Product, a.θ = θa ∧ t.θ = θt ∧ t.q = qt ∧ qlow ≤ a.q ∧
          ubar ≤ u a ∧ Fools β β0 a t ∧ qt - ubar < t.p) ∧
      -- Moreover: with (Q,Q) fooling up-sells, with (P,P) it down-sells,
      (∀ a t : Product, a.θ = Ctx.Q → t.θ = Ctx.Q → Fools β β0 a t → a.q < t.q ∧ a.p < t.p) ∧
      (∀ a t : Product, a.θ = Ctx.P → t.θ = Ctx.P → Fools β β0 a t → t.q < a.q ∧ t.p < a.p) ∧
      -- and contexts favouring the attraction product cannot fool at any p_t ≥ 0
      (∀ a t : Product,
          (a.θ, t.θ) = (Ctx.Q, Ctx.P) ∨ (a.θ, t.θ) = (Ctx.Q, Ctx.N) ∨ (a.θ, t.θ) = (Ctx.N, Ctx.P) →
          qlow ≤ a.q → 0 ≤ t.p → ¬ Fools β β0 a t)) := by sorry

end ContextFooling.FoolingEq
