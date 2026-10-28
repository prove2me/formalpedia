-- Prove2me | Theorems.Thm_ContextFooling_FoolingEq_lemma_2
-- name    : ContextFooling.FoolingEq.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T05:48:38.848053+00:00
-- url     : https://prove2.me/theorems/ca480222-e448-4aa5-a5d0-bc84c2e91965
-- title:
--   Lemma 2, p. 12 (PDF 13) — a fooling pair distorts some context, needs β̃⁰ ≠ β, never fools optimists and pessimists alike, and lowers u_t for optimists
-- statement:
--   Let $\beta>1$ and let $\tilde\beta^0>1$ be a consumer type. Suppose the pair $(a,t)$ fools type $\tilde\beta^0$ in the sense of Definition 3: $a\ne t$, (IC) $\hat u_t(\beta)\ge\hat u_a(\beta)$ and (PCC) $\hat u_t(\tilde\beta^0)\le\hat u_a(\tilde\beta^0)$, with at least one of them strict. Then:
--   1. the context distorts at least one of the two products: $(\theta_a,\theta_t)\ne(N,N)$;
--   2. the fooled type is naïve: $\tilde\beta^0\ne\beta$;
--   3. if she is a pessimist ($\tilde\beta^0>\beta$), every optimist expects to prefer the target, and the target gives more undistorted surplus:
--   $$\forall\tilde\beta<\beta:\ \hat u_t(\tilde\beta)>\hat u_a(\tilde\beta),\qquad u_t>u_a;$$
--   4. if she is an optimist ($\tilde\beta^0<\beta$), every pessimist expects to prefer the target, and the target gives less undistorted surplus:
--   $$\forall\tilde\beta>\beta:\ \hat u_t(\tilde\beta)>\hat u_a(\tilde\beta),\qquad u_t<u_a.$$
--
--   Part 4 is the reason fooling optimists can be profitable: a fooled optimist buys a product of lower undistorted surplus than the one that attracted her.
--
--   **Formalization Note.** The hypothesis $\tilde\beta^0>1$ is the paper's $f(\tilde\beta)=0$ for $\tilde\beta\le 1$ (p. 7); the proof uses it ("by $\gamma_0>1$"), and the optimist's strict inequality $u_t<u_a$ fails at $\tilde\beta^0=1$. "Target of firm $k$" is read at the level of the pair: the statement is about any fooling pair.
-- source:
--   Apffelstaedt & Mechtenberg, Competition for Context-Sensitive Consumers, MPRA Paper No. 99509 (version of November 2016; published in Management Science, doi:10.1287/mnsc.2020.3675), p. 12 (PDF 13), Lemma 2; proof pp. 35–37 (PDF 36–38)

import Mathlib
import Definitions.Def_ContextFooling_FoolingEq_Model

namespace ContextFooling.FoolingEq

/-- Lemma 2 (Naïveté and Fooling), p. 12. A fooling pair (a, t) distorts some context, needs a
naïve type, is seen through by the other kind of naïf, and moves undistorted surplus. -/
theorem lemma_2 (β β0 : ℝ) (hβ : 1 < β) (hβ0 : 1 < β0) (a t : Product)
    (hfool : Fools β β0 a t) :
    (a.θ, t.θ) ≠ (Ctx.N, Ctx.N) ∧ β0 ≠ β ∧
    (β < β0 → (∀ γ : ℝ, γ < β → val γ a < val γ t) ∧ u a < u t) ∧
    (β0 < β → (∀ γ : ℝ, β < γ → val γ a < val γ t) ∧ u t < u a) := by sorry

end ContextFooling.FoolingEq
