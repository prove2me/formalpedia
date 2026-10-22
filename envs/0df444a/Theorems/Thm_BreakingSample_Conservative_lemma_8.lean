-- Prove2me | Theorems.Thm_BreakingSample_Conservative_lemma_8
-- name    : BreakingSample.Conservative.lemma_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T11:03:57.335786+00:00
-- url     : https://prove2.me/theorems/023995e8-c481-41e6-908e-ec8c2214d348
-- title:
--   Lemma 8, p. 19 — w.p. ≥ 1 − δ over ς ∼ Unif(0,ξ), {a : Q̂(s,a) > V̂(s) − ς} is unchanged for every Q within ξδ/(8|S||A|) of Q̂
-- statement:
--   Let $\mathcal S$, $\mathcal A$ be finite with $\mathcal A$ nonempty, let $\widehat Q : \mathcal S\times\mathcal A\to\mathbb R$ be any Q-function and $\widehat V(s) = \max_a \widehat Q(s,a)$ its associated value function, and let $\xi > 0$, $\delta > 0$. Draw $\varsigma \sim \mathrm{Unif}(0,\xi)$. Then with probability at least $1-\delta$ the following holds simultaneously for **all** Q-functions $Q$ (with associated value function $V(s) = \max_a Q(s,a)$) obeying
--
--   $$\max_{s,a} \big|Q(s,a) - \widehat Q(s,a)\big| \le \frac{\xi\delta}{8|\mathcal S||\mathcal A|}:$$
--
--   $$\forall s \in \mathcal S, \qquad \{a \in \mathcal A : \widehat Q(s,a) > \widehat V(s) - \varsigma\} = \{a\in\mathcal A : Q(s,a) > V(s) - \varsigma\}.$$
--
--   Consequently the conservative policy computed from $\widehat Q$ does not change under small perturbations of $\widehat Q$, which is what allows it to be represented by policies independent of the samples of one pair $(s,a)$.
--
--   **Formalization Note** The probability is the $\mathrm{Unif}(0,\xi)$ measure (outer measure if not measurable) of the failure event, bounded by $\delta$. The quantifier over $Q$ is inside the event.
-- source:
--   arXiv:2005.12900v8, Lemma 8, p. 19, (54)–(55); proof in App. B.7, pp. 33–34

import Mathlib
import Definitions.Def_BreakingSample_Perturbed_Sampling
import Definitions.Def_BreakingSample_Conservative_Rule

namespace BreakingSample.Conservative

theorem lemma_8 {S A : Type} [Fintype S] [Fintype A] [Nonempty A]
    (Qhat : S → A → ℝ) (ξ δ : ℝ) (hξ : 0 < ξ) (hδ : 0 < δ) :
    BreakingSample.Perturbed.unifInterval ξ {ς : ℝ | ¬ ∀ Q : S → A → ℝ,
        (∀ s a, |Q s a - Qhat s a| ≤ ξ * δ / (8 * (Fintype.card S : ℝ) * (Fintype.card A : ℝ))) →
        ∀ s, {a : A | maxQ Qhat s - ς < Qhat s a} = {a : A | maxQ Q s - ς < Q s a}}
      ≤ ENNReal.ofReal δ := by sorry

end BreakingSample.Conservative
