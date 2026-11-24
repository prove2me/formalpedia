-- Prove2me | Theorems.Thm_DisentanglementImpossibility_impossibility_theorem
-- name    : DisentanglementImpossibility.impossibility_theorem
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T07:32:19.619097+00:00
-- url     : https://prove2.me/theorems/78ed6cbd-5481-477e-a9fa-64738883b180
-- title:
--   Theorem 1: impossibility of unsupervised disentanglement
-- statement:
--   Let $d>1$, and let $z\sim P$ be a random vector in $\mathbb{R}^d$ whose law admits a density $p(z)=\prod_{i=1}^dp(z_i)$, so that its coordinates $z_i\sim\mu_i$ are independent and each has a Lebesgue density. Then there is an infinite sequence $f^{(1)},f^{(2)},\dots$ of maps, pairwise different on $\operatorname{supp}(z)$, such that each $f=f^{(n)}$ satisfies:
--
--   1. $f$ is measurable and is a bijection $\operatorname{supp}(z)\to\operatorname{supp}(z)$;
--   2. $z$ and $f(z)$ are completely entangled: for all $i,j$ and $P$-almost every $u$, the partial derivative $\partial f_i(u)/\partial u_j$ of $f$, as a map on $\operatorname{supp}(z)$, exists and
--   $$\frac{\partial f_i(u)}{\partial u_j}\ne0;$$
--   3. $z$ and $f(z)$ have the same distribution function on the support:
--   $$P(z\le u)=P(f(z)\le u)\qquad\text{for all }u\in\operatorname{supp}(z).$$
--
--   Consequently, a generative model with latent $z$ and the model with latent $\hat z=f(z)$ induce the same distribution of observations, while every coordinate of $\hat z$ depends on every coordinate of $z$. An unsupervised method, which only sees observations, cannot distinguish the two models.
--
--   **Formalization Note** (a) No condition on the supports is assumed, as in the paper. The paper's proof asserts that $g$ is bijective, which is false when a marginal support has a gap, for example $[0,1]\cup[2,3]$. The theorem still holds: the paper's map is first conjugated by a bijection of $\operatorname{supp}(z)$ that moves only countably many coordinate values, along short chains starting at the right endpoints of the gaps. (b) "Almost everywhere" is taken with respect to $P$. Under Lebesgue measure on $\operatorname{supp}(z)$ the proof's construction fails when a density vanishes on a set of positive measure inside its support. (c) The partial derivatives of $f:\operatorname{supp}(z)\to\operatorname{supp}(z)$ are taken along the support. (d) The infinite family is an injective sequence, with distinctness required on $\operatorname{supp}(z)$ because values off the support are irrelevant. (e) Measurability of $f$ is the standing convention that $f(z)$ is a random variable.
-- source:
--   Locatello, Bauer, Lucic, Rätsch, Gelly, Schölkopf, Bachem, Challenging Common Assumptions in the Unsupervised Learning of Disentangled Representations, ICML 2019, arXiv:1811.12359v4, Section 3, Theorem 1, p. 3; proof in Appendix A, p. 12

import Mathlib
import Definitions.Def_DisentanglementImpossibility_Basic

open MeasureTheory ProbabilityTheory

namespace DisentanglementImpossibility

theorem impossibility_theorem {d : ℕ} (hd : 1 < d) (μ : Fin d → Measure ℝ)
    (hμ : IsFactorizedDensity μ) :
    ∃ f : ℕ → (Fin d → ℝ) → Fin d → ℝ,
      (∀ m n, m ≠ n → ∃ u ∈ (latentLaw μ).support, f m u ≠ f n u) ∧
      ∀ n,
        Measurable (f n) ∧
        Set.BijOn (f n) (latentLaw μ).support (latentLaw μ).support ∧
        (∀ i j, ∀ᵐ u ∂(latentLaw μ), partialDerivWithin (f n) (latentLaw μ).support i j u ≠ 0) ∧
        (∀ u ∈ (latentLaw μ).support,
          latentLaw μ {z | z ≤ u} = latentLaw μ {z | f n z ≤ u}) := by sorry

end DisentanglementImpossibility
