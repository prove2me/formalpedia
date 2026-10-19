-- Prove2me | Theorems.Thm_ConfoundRobust_Minimax_theorem_6
-- name    : ConfoundRobust.Minimax.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:12:12.909984+00:00
-- url     : https://prove2.me/theorems/cf7c710d-09be-4360-81d2-557a461ccf9b
-- title:
--   Theorem 6, p. 15, as proved on p. 44 — sup_π |R̄̂(π; 𝒲^Γ_n) − R̄(π; 𝒲^Γ)| ≤ 18(12+ν⁻¹)(BK+ν⁻¹(Γ−Γ⁻¹)(K+B+m))√(log(15m/δ)/n)
-- statement:
--   For every $v \in \mathbb N$ there is a constant $K$, depending only on $v$, with the following property. Let $\mu$ be the law of $(X,T,Y)$ with $m \ge 2$ treatments; let $\tilde e$ be its nominal propensity with $\nu \le \tilde e_t(x) \le 1$ for some $\nu > 0$ (overlap); let $|Y| \le B$ almost surely (Assumption 1); let $\Gamma \ge 1$; let $\Pi$ be a class of policies of VC-major dimension at most $v$ (Assumption 3), pointwise separable as a class of functions $(t,x)\mapsto\pi(t\mid x)$, and $\pi_0$ a baseline policy. Then for every $n \ge 1$ and $\delta \in (0,1)$, with probability at least $1-\delta$ over an iid sample of size $n$,
--   $$\sup_{\pi \in \Pi} \Big| \hat{\bar R}_{\pi_0}(\pi; \mathcal W^\Gamma_n) - \bar R_{\pi_0}(\pi; \mathcal W^\Gamma) \Big| \le 18\,(12 + \nu^{-1})\big(BK + \nu^{-1}(\Gamma - \Gamma^{-1})(K + B + m)\big) \sqrt{\frac{\log(15m/\delta)}{n}} .$$
--
--   This is the uniform convergence of the worst-case empirical regret to the worst-case population regret over the policy class, the key estimate behind the minimax guarantee of Corollary 7.
--
--   **Formalization Note** The constant is $18$, the constant at the end of the paper's proof (p. 44), where the dimension-dependent factors $\sqrt{K_\pi(v_\pi+2)}$ and $2\sqrt{K_{u\circ\pi}(v_{u\circ\pi}+2)}$ are collected into one $K$. The printed Theorem 6 has $36$ and follows from this statement. The page's "$\log(15m/p)$" is read with $p = \delta$. Assumption 2 (overlap of the true propensity, $e_t(x,y) \ge \nu$) enters only through its observable consequence $\tilde e_t(x) = \mathbb E[e_t(X, Y(t)) \mid X = x] \ge \nu$, so the formal hypothesis is weaker than the paper's and the statement at least as strong; $\tilde e \le 1$ holds for any version of a conditional probability that is chosen $[0,1]$-valued. "With probability at least $1-\delta$" is a measurable event of product measure $\ge 1-\delta$ on which the bound holds for every $\pi \in \Pi$. The constant $K$ is chosen before everything except $v$. An empty treatment group in the sample gives the Hájek ratio $0/0 = 0$. **Measurability of the class.** The hypothesis that $\Pi$, as a class of functions $(t,x)\mapsto\pi(t\mid x)$, is pointwise separable (a countable subclass approximates every member pointwise; van der Vaart and Wellner 1996, Example 2.3.4) is not printed in the paper. It is the standard measurability condition under which the symmetrization and chaining tools the paper's proof uses hold, and it is necessary: on an uncountable well-ordered set of type $\omega_1$ with the countable–cocountable probability measure, the policies $\pi_\alpha(1\mid x) = \mathbb 1\{x \le \alpha\}$ form a class of VC-major dimension at most $2$, each $\pi_\alpha$ agrees almost surely with "never treat", yet $\alpha = \max_i X_i$ makes the empirical and population quantities differ by a fixed amount for every sample, so the statement without this hypothesis is false. Linear, logistic and finite-depth tree classes with real parameters are pointwise separable (rational parameters).
-- source:
--   Kallus & Zhou, arXiv:1805.08593v3, Theorem 6, p. 15; proof of Theorem 6 (Appendix B.2), last display, p. 44

import Mathlib
import Definitions.Def_ConfoundRobust_Minimax_Setting

open MeasureTheory

namespace ConfoundRobust.Minimax

theorem theorem_6 :
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
        ∀ ω ∈ E, ∀ π ∈ Pol,
          |sWorstRegret ω π π0 (WSetN Γ e ω) - worstRegret μ π π0 (WSet Γ e)| ≤
            rateThm6 ν B Γ K m n δ := by sorry

end ConfoundRobust.Minimax
