-- Prove2me | Theorems.Thm_AlignmentUniformity_contrastive_limit_and_rate
-- name    : AlignmentUniformity.contrastive_limit_and_rate
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T17:31:22.962626+00:00
-- url     : https://prove2.me/theorems/44e8f42f-d931-4bba-8e42-29d17865afe5
-- title:
--   Theorem 1 (eq. (2) and result 3): the limit of $\mathcal{L}_\mathsf{contrastive} - \log M$ and its $O(M^{-1/2})$ rate
-- statement:
--   Let $m\ge1$ and $\tau>0$. Let $p_{\mathrm{data}}$ be a probability distribution on $\mathbb{R}^n$ and $p_{\mathrm{pos}}$ a symmetric probability distribution on $\mathbb{R}^n\times\mathbb{R}^n$ with marginal $p_{\mathrm{data}}$. Let $f:\mathbb{R}^n\to S^{m-1}$ be a measurable encoder. Then, as the number $M$ of negative samples tends to infinity,
--
--   $$\lim_{M\to\infty}\mathcal{L}_{\mathsf{contrastive}}(f;\tau,M)-\log M=-\frac1\tau\mathbb{E}_{(x,y)\sim p_{\mathrm{pos}}}[f(x)^\top f(y)]+\mathbb{E}_{x\sim p_{\mathrm{data}}}\Big[\log\mathbb{E}_{x^-\sim p_{\mathrm{data}}}\big[e^{f(x^-)^\top f(x)/\tau}\big]\Big],$$
--
--   and the deviation from the limit is $O(M^{-1/2})$: there is a constant $C$ with
--
--   $$\Big|\mathcal{L}_{\mathsf{contrastive}}(f;\tau,M)-\log M-\text{(limit)}\Big|\le\frac{C}{\sqrt M}\qquad\text{for all }M\ge1.$$
--
--   This is eq. (2) together with result 3 of Theorem 1.
--
--   **Formalization Note** The constant $C$ may depend on $f$, $\tau$, $p_{\mathrm{data}}$ and $p_{\mathrm{pos}}$, as in the paper's $O(\cdot)$ for fixed $f$ and $\tau$.
-- source:
--   Wang and Isola, Understanding Contrastive Representation Learning through Alignment and Uniformity on the Hypersphere, ICML 2020, arXiv:2005.10242v10, Section 4.2, Theorem 1, eq. (2) and result 3, p. 6; proof in Appendix A.2, eqs. (10)-(11), pp. 19-20

import Mathlib
import Definitions.Def_AlignmentUniformity_Basic

open MeasureTheory Filter Topology

namespace AlignmentUniformity

theorem contrastive_limit_and_rate {n m : ℕ} (hm : 1 ≤ m) {τ : ℝ} (hτ : 0 < τ)
    (pdata : Measure (Vec n)) [IsProbabilityMeasure pdata]
    (ppos : Measure (Vec n × Vec n)) [IsProbabilityMeasure ppos] (hpos : IsPosPairLaw pdata ppos)
    (f : Vec n → Vec m) (hf : IsEncoder f) :
    Tendsto (fun M : ℕ => contrastiveLoss pdata ppos f τ M - Real.log M) atTop
        (𝓝 (alignTerm ppos f τ + uniformTerm pdata f τ)) ∧
      ∃ C : ℝ, ∀ M : ℕ, 1 ≤ M →
        |contrastiveLoss pdata ppos f τ M - Real.log M -
            (alignTerm ppos f τ + uniformTerm pdata f τ)| ≤ C / Real.sqrt M := by sorry

end AlignmentUniformity
