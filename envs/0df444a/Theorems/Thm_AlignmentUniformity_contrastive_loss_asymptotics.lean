-- Prove2me | Theorems.Thm_AlignmentUniformity_contrastive_loss_asymptotics
-- name    : AlignmentUniformity.contrastive_loss_asymptotics
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T17:33:17.709158+00:00
-- url     : https://prove2.me/theorems/0c328eb0-a351-4123-94c9-7789403a1b90
-- title:
--   Theorem 1: asymptotics of $\mathcal{L}_\mathsf{contrastive}$
-- statement:
--   Let $m\ge1$ and $\tau>0$. Let $p_{\mathrm{data}}$ be a probability distribution on $\mathbb{R}^n$, and let $p_{\mathrm{pos}}$ be a probability distribution on $\mathbb{R}^n\times\mathbb{R}^n$ satisfying the Assumption of Section 3: it is symmetric and its marginal is $p_{\mathrm{data}}$. Encoders are measurable maps $\mathbb{R}^n\to S^{m-1}$. For every encoder $f$, the normalized contrastive loss converges as the number $M$ of negative samples tends to infinity:
--
--   $$\lim_{M\to\infty}\mathcal{L}_{\mathsf{contrastive}}(f;\tau,M)-\log M=\underbrace{-\frac1\tau\mathbb{E}_{(x,y)\sim p_{\mathrm{pos}}}[f(x)^\top f(y)]}_{\text{first term}}+\underbrace{\mathbb{E}_{x\sim p_{\mathrm{data}}}\Big[\log\mathbb{E}_{x^-\sim p_{\mathrm{data}}}\big[e^{f(x^-)^\top f(x)/\tau}\big]\Big]}_{\text{second term}}.$$
--
--   Moreover:
--
--   1. The first term is minimized over all encoders if and only if $f$ is perfectly aligned.
--   2. If some perfectly uniform encoder exists, then an encoder minimizes the second term over all encoders if and only if it is perfectly uniform.
--   3. The absolute deviation from the limit is $O(M^{-1/2})$: there is a constant $C$ such that, for all $M\ge1$, $\big|\mathcal{L}_{\mathsf{contrastive}}(f;\tau,M)-\log M-\text{(limit)}\big|\le C/\sqrt M$.
--
--   The theorem shows that, with many negative samples, the contrastive loss optimizes alignment of positive pairs and uniformity of the feature distribution on the sphere.
--
--   **Formalization Note** The constant in item 3 may depend on $f$, $\tau$ and the distributions, as the paper's $O(\cdot)$ does for fixed $f$ and $\tau$. The distributions are probability measures rather than densities.
-- source:
--   Wang and Isola, Understanding Contrastive Representation Learning through Alignment and Uniformity on the Hypersphere, ICML 2020, arXiv:2005.10242v10, Section 4.2, Theorem 1, eq. (2), p. 6; Assumption of Section 3, p. 3; proof in Appendix A.2, pp. 19-24

import Mathlib
import Definitions.Def_AlignmentUniformity_Basic

open MeasureTheory Filter Topology

namespace AlignmentUniformity

theorem contrastive_loss_asymptotics {n m : ℕ} (hm : 1 ≤ m) {τ : ℝ} (hτ : 0 < τ)
    (pdata : Measure (Vec n)) [IsProbabilityMeasure pdata]
    (ppos : Measure (Vec n × Vec n)) [IsProbabilityMeasure ppos] (hpos : IsPosPairLaw pdata ppos)
    (f : Vec n → Vec m) (hf : IsEncoder f) :
    Tendsto (fun M : ℕ => contrastiveLoss pdata ppos f τ M - Real.log M) atTop
        (𝓝 (alignTerm ppos f τ + uniformTerm pdata f τ)) ∧
      ((∀ g : Vec n → Vec m, IsEncoder g → alignTerm ppos f τ ≤ alignTerm ppos g τ) ↔
        PerfectlyAligned ppos f) ∧
      ((∃ g : Vec n → Vec m, IsEncoder g ∧ PerfectlyUniform pdata g) →
        ((∀ g : Vec n → Vec m, IsEncoder g → uniformTerm pdata f τ ≤ uniformTerm pdata g τ) ↔
          PerfectlyUniform pdata f)) ∧
      ∃ C : ℝ, ∀ M : ℕ, 1 ≤ M →
        |contrastiveLoss pdata ppos f τ M - Real.log M -
            (alignTerm ppos f τ + uniformTerm pdata f τ)| ≤ C / Real.sqrt M := by sorry

end AlignmentUniformity
