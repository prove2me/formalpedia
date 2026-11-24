-- Prove2me | Theorems.Thm_DisentanglementImpossibility_cdf_map_uniform
-- name    : DisentanglementImpossibility.cdf_map_uniform
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T07:28:44.633923+00:00
-- url     : https://prove2.me/theorems/fd0165ee-24d2-4031-8a3a-78cf7a6e77e8
-- title:
--   Theorem 1 (proof, map $g$): the coordinatewise CDF map makes the latent uniform
-- statement:
--   Let $d\ge0$ be any dimension, and let $z=(z_1,\dots,z_d)$ have law $P=\mu_1\otimes\cdots\otimes\mu_d$, where each $\mu_i$ is a probability measure on $\mathbb{R}$ with a Lebesgue density. Let $F_i$ be the distribution function of $\mu_i$ and $g(v)=(F_1(v_1),\dots,F_d(v_d))$. Then:
--
--   1. $g(z)$ is uniformly distributed on $[0,1]^d$, with independent coordinates;
--   2. for every $i$, for $P$-almost every $v$, the derivative $\partial g_i(v)/\partial v_i=F_i'(v_i)$ exists and is nonzero;
--   3. $\partial g_i(v)/\partial v_j=0$ for all $i\ne j$ and all $v$;
--   4. if the support of every $\mu_i$ is an interval, then $g$ is injective on $\operatorname{supp}(z)$.
--
--   This is the first step of the proof of Theorem 1, the probability integral transform applied coordinatewise.
--
--   **Formalization Note** The paper says "for almost every $v\in\operatorname{supp}(z)$" without naming the measure. Item 2 uses $P$. With Lebesgue measure on $\operatorname{supp}(z)$ it fails, because a density can vanish on a subset of the support of positive Lebesgue measure. The paper also asserts that $g$ is bijective for every factorized density. That fails when some $\mu_i$ has a support with a gap: for $\mu_i$ uniform on $[0,1]\cup[2,3]$, $F_i(1)=F_i(2)=1/2$. Item 4 is the injectivity under the interval-support condition, which is the case the proof of Theorem 1 covers.
-- source:
--   Locatello, Bauer, Lucic, Rätsch, Gelly, Schölkopf, Bachem, Challenging Common Assumptions in the Unsupervised Learning of Disentangled Representations, ICML 2019, arXiv:1811.12359v4, Appendix A (Proof of Theorem 1), definition of g and the two sentences after it, p. 12

import Mathlib
import Definitions.Def_DisentanglementImpossibility_Basic

open MeasureTheory ProbabilityTheory

namespace DisentanglementImpossibility

theorem cdf_map_uniform {d : ℕ} (μ : Fin d → Measure ℝ) (hμ : IsFactorizedDensity μ) :
    (latentLaw μ).map (cdfMap μ) = uniformCube d ∧
    (∀ i, ∀ᵐ v ∂(latentLaw μ), deriv (fun t => cdf (μ i) t) (v i) ≠ 0) ∧
    (∀ i j, i ≠ j → ∀ v, partialDeriv (cdfMap μ) i j v = 0) ∧
    ((∀ i, (μ i).support.OrdConnected) → Set.InjOn (cdfMap μ) (latentLaw μ).support) := by sorry

end DisentanglementImpossibility
