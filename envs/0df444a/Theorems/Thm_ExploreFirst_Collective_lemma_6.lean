-- Prove2me | Theorems.Thm_ExploreFirst_Collective_lemma_6
-- name    : ExploreFirst.Collective.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:03:59.654882+00:00
-- url     : https://prove2.me/theorems/d861d739-4207-4f5d-a6c7-b4163d60f2d2
-- title:
--   Lemma 6, p. 20 — $\mathrm{kl}(p,q)\ge(p-q)^2/(2\max_{[p,q]}x(1-x))\ge(p-q)^2/(2q)$
-- statement:
--   This is a local refinement of Pinsker's inequality for Bernoulli distributions.
--
--   Let $\mathrm{kl}(p,q)$ be the Kullback–Leibler divergence between Bernoulli distributions of parameters $p$ and $q$, as in (5). For $0\le p<q\le1$,
--   $$\mathrm{kl}(p,q)\ \ge\ \frac{1}{2\max_{x\in[p,q]}x(1-x)}\,(p-q)^2\ \ge\ \frac{1}{2q}\,(p-q)^2.$$
--
--   The classical form $\mathrm{kl}(p,q)\ge2(p-q)^2$ follows from $x(1-x)\le1/4$. The proof of Theorem 4 uses the outer inequality $\mathrm{kl}(p,q)\ge(p-q)^2/(2q)$, which is sharper when $q$ is small.
--
--   **Formalization Note** $\mathrm{kl}$ takes values in $[0,+\infty]$ (it is $+\infty$ at $q=1$, $p<1$), so the first inequality is stated in $[0,+\infty]$ for the nonnegative real $(p-q)^2/(2\max)$, and the second inequality between the two real lower bounds is stated in $\mathbb R$. The maximum of $x(1-x)$ over the compact interval $[p,q]$ is written as a supremum of its image; it is attained and positive.
-- source:
--   Garivier, Ménard, Stoltz, Explore First, Exploit Next, arXiv:1602.07182v3, p. 20, Appendix A, Lemma 6

import Mathlib
import Definitions.Def_ExploreFirst_Collective_Setting

namespace ExploreFirst.Collective

open MeasureTheory ProbabilityTheory BanditAlgorithm
open scoped ENNReal

/-- Lemma 6, p. 20 (local refinement of Pinsker's inequality): for `0 ≤ p < q ≤ 1`,
`kl(p, q) ≥ (p - q)² / (2 max_{x ∈ [p, q]} x(1 - x)) ≥ (p - q)² / (2q)`. -/
theorem lemma_6 (p q : ℝ) (hp : 0 ≤ p) (hpq : p < q) (hq : q ≤ 1) :
    ENNReal.ofReal ((p - q) ^ 2 / (2 * sSup ((fun x => x * (1 - x)) '' Set.Icc p q)))
        ≤ ExploreFirst.FundIneq.klBer p q ∧
      (p - q) ^ 2 / (2 * q) ≤ (p - q) ^ 2 / (2 * sSup ((fun x => x * (1 - x)) '' Set.Icc p q)) := by sorry

end ExploreFirst.Collective
