-- Prove2me | Theorems.Thm_BoundedNV_Pooling_canon_profit_nonpos
-- name    : BoundedNV.Pooling.canon_profit_nonpos
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:57:33.095957+00:00
-- url     : https://prove2.me/theorems/b65dfab5-0c03-4c2a-b8b3-e2eeffffee92
-- title:
--   Proof of Proposition 7, eq. (66), pp. 587–588 — the canonical optimum and nonpositivity of the canonical profit
-- statement:
--   Let $Z$ be standard normal, with density $\phi$ and distribution function $\Phi$, and let the selling price $p$ and acquisition cost $c$ satisfy $0<c<p$. The canonical profit of a standardized order $z\in\mathbb R$ is $\Pi(z)=p\,\mathbb E[\min(Z,z)]-cz$. The canonical newsvendor problem $\max_z \Pi(z)$ has a solution; every solution $z^*$ satisfies
--
--   $$
--   \Phi(z^*)=1-\frac{c}{p},\qquad \Pi(z^*)=p\int_{-\infty}^{z^*} v\,\phi(v)\,dv,
--   $$
--
--   and $\Pi(z)\leq 0$ for every $z\in\mathbb R$.
--
--   This sign is the ingredient that turns the bound on pooled demand's standard deviation into a cost comparison.
--
--   **Formalization Note** The paper's equation (66) omits $\min$ typographically. The expression above follows its surrounding equations and the stated conclusion.
-- source:
--   Su, Bounded Rationality in Newsvendor Models, Manufacturing & Service Operations Management 10(4), 2008, pp. 587–588 (PDF 22–23), proof of Proposition 7, eq. (66) and sentence following

import Mathlib
import Definitions.Def_BoundedNV_Pooling_Canonical

open MeasureTheory ProbabilityTheory

namespace BoundedNV.Pooling

/-- Proof of Proposition 7, eq. (66), pp. 587–588: the canonical problem has a solution, every maximizer `z*` of the canonical profit
satisfies `Φ(z*) = 1 − c/p` and `Π(z*) = p ∫_{-∞}^{z*} v φ(v) dv`, and the canonical profit is
nonpositive everywhere. -/
theorem canon_profit_nonpos (p c : ℝ) (hc : 0 < c) (hcp : c < p) :
    (∃ zstar : ℝ, IsMaxOn (canonProfit p c) Set.univ zstar) ∧
    (∀ zstar : ℝ, IsMaxOn (canonProfit p c) Set.univ zstar →
      cdf (gaussianReal 0 1) zstar = 1 - c / p ∧
        canonProfit p c zstar = p * ∫ v in Set.Iic zstar, v * gaussianPDFReal 0 1 v) ∧
    ∀ z : ℝ, canonProfit p c z ≤ 0 := by sorry

end BoundedNV.Pooling
