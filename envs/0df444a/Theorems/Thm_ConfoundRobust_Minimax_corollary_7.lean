-- Prove2me | Theorems.Thm_ConfoundRobust_Minimax_corollary_7
-- name    : ConfoundRobust.Minimax.corollary_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:12:11.581269+00:00
-- url     : https://prove2.me/theorems/ae7539c0-7239-4556-896b-76112ad0a10a
-- title:
--   Corollary 7, p. 15 — w.p. ≥ 1 − δ the worst-case-regret minimizer is within 36(12+ν⁻¹)(BK+ν⁻¹(Γ−Γ⁻¹)(K+B+m))√(log(15m/δ)/n) of the population minimax regret
-- statement:
--   For every $v \in \mathbb N$ there is a constant $K$, depending only on $v$, with the following property. Let $\mu$ be the law of $(X,T,Y)$ with $m \ge 2$ treatments; let $\tilde e$ be its nominal propensity with $\nu \le \tilde e_t(x) \le 1$ for some $\nu > 0$ (overlap); let $|Y| \le B$ almost surely (Assumption 1); let $\Gamma \ge 1$; let $\Pi$ be a class of policies of VC-major dimension at most $v$ (Assumption 3), pointwise separable as a class of functions $(t,x)\mapsto\pi(t\mid x)$, and $\pi_0$ a baseline policy. Then for every $n \ge 1$ and $\delta \in (0,1)$, with probability at least $1-\delta$ over an iid sample of size $n$, every policy $\hat{\bar\pi} \in \Pi$ that minimizes the worst-case empirical regret $\hat{\bar R}_{\pi_0}(\cdot\,; \mathcal W^\Gamma_n)$ over $\Pi$ satisfies
--   $$\bar R_{\pi_0}(\hat{\bar\pi}; \mathcal W^\Gamma) \le \inf_{\pi \in \Pi} \bar R_{\pi_0}(\pi; \mathcal W^\Gamma) + 36\,(12 + \nu^{-1})\big(BK + \nu^{-1}(\Gamma - \Gamma^{-1})(K + B + m)\big) \sqrt{\frac{\log(15m/\delta)}{n}} .$$
--   Here $\bar R_{\pi_0}(\pi; \mathcal W^\Gamma)$ is the worst-case population regret of $\pi$ against $\pi_0$ over all weight functions allowed by the marginal sensitivity model with parameter $\Gamma$, and $\inf_{\pi\in\Pi}$ of it is the population minimax regret.
--
--   The policy learned by minimizing the worst-case empirical regret is therefore minimax-optimal up to an explicit $O(n^{-1/2})$ term: no other policy in the class has a better guarantee against every confounding pattern consistent with the sensitivity model, up to that term.
--
--   **Formalization Note** $\hat{\bar\pi}$ is any minimizer of the worst-case empirical regret over $\Pi$ (display (5)); the paper assumes one exists, and at a sample without a minimizer the conclusion is vacuous. "With probability at least $1-\delta$" is a measurable event of product measure $\ge 1-\delta$ on which the conclusion holds. The constant $K$ is chosen before everything except $v$. Assumption 2 enters only through its observable consequence $\nu \le \tilde e_t(x)$ (see Theorem 6); an empty treatment group gives the Hájek ratio $0/0 = 0$. The infimum is the real infimum over $\Pi$, taken over a nonempty bounded set whenever a minimizer exists. **Measurability of the class.** The hypothesis that $\Pi$, as a class of functions $(t,x)\mapsto\pi(t\mid x)$, is pointwise separable (a countable subclass approximates every member pointwise; van der Vaart and Wellner 1996, Example 2.3.4) is not printed in the paper. It is the standard measurability condition under which the symmetrization and chaining tools the paper's proof uses hold, and it is necessary: on an uncountable well-ordered set of type $\omega_1$ with the countable–cocountable probability measure, the policies $\pi_\alpha(1\mid x) = \mathbb 1\{x \le \alpha\}$ form a class of VC-major dimension at most $2$, each $\pi_\alpha$ agrees almost surely with "never treat", yet $\alpha = \max_i X_i$ makes the empirical and population quantities differ by a fixed amount for every sample, so the statement without this hypothesis is false. Linear, logistic and finite-depth tree classes with real parameters are pointwise separable (rational parameters).
-- source:
--   Kallus & Zhou, arXiv:1805.08593v3, Corollary 7, p. 15

import Mathlib
import Definitions.Def_ConfoundRobust_Minimax_Setting

open MeasureTheory

namespace ConfoundRobust.Minimax

theorem corollary_7 :
    ∀ v : ℕ, ∃ K : ℝ, ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (m n : ℕ), 2 ≤ m → 0 < n →
      ∀ (μ : Measure (Obs 𝒳 m)) [IsProbabilityMeasure μ]
        (e : Fin m → 𝒳 → ℝ) (ν : ℝ), IsNominalPropensity μ e → 0 < ν →
        (∀ t x, ν ≤ e t x) → (∀ t x, e t x ≤ 1) →
      ∀ B : ℝ, 0 ≤ B → (∀ᵐ z ∂μ, |z.2.2| ≤ B) →
      ∀ Γ : ℝ, 1 ≤ Γ →
      ∀ Pol : Set (𝒳 → Fin m → ℝ), (∀ π ∈ Pol, IsPolicy π) → VCMajorLE (policyFns Pol) v →
        PointwiseSeparable (policyFns Pol) →
      ∀ π0 : 𝒳 → Fin m → ℝ, IsPolicy π0 →
      ∀ δ : ℝ, 0 < δ → δ < 1 →
      ∃ E : Set (Fin n → Obs 𝒳 m), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ) ≤ Measure.pi (fun _ : Fin n => μ) E ∧
        ∀ ω ∈ E, ∀ πh ∈ Pol,
          (∀ π ∈ Pol, sWorstRegret ω πh π0 (WSetN Γ e ω) ≤ sWorstRegret ω π π0 (WSetN Γ e ω)) →
          worstRegret μ πh π0 (WSet Γ e) ≤
            sInf ((fun π => worstRegret μ π π0 (WSet Γ e)) '' Pol) + rateCor7 ν B Γ K m n δ := by sorry

end ConfoundRobust.Minimax
