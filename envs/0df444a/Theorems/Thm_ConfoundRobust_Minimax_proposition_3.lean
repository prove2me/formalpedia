-- Prove2me | Theorems.Thm_ConfoundRobust_Minimax_proposition_3
-- name    : ConfoundRobust.Minimax.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:12:03.014959+00:00
-- url     : https://prove2.me/theorems/4a065a09-4b9f-444d-8a4b-dc80a5c039a3
-- title:
--   Proposition 3, pp. 14–15 — the worst-case regret is a sum over treatments of sups over monotone threshold weights
-- statement:
--   Let $\mu$ be the law of $(X,T,Y)$ with $m \ge 2$ treatments, $\tilde e$ its nominal propensity with $\nu \le \tilde e_t(x) \le 1$ for some $\nu > 0$, $|Y| \le B$ almost surely, $\Gamma \ge 1$, and $\pi_0$ a baseline policy. For every policy $\pi$, the worst-case regret over the box $\mathcal W^\Gamma$ decomposes over treatments, and each treatment's worst case is attained among the monotone weights $\bar{\mathcal W}^\Gamma(\pi)$; the same holds for the sample worst case, for every sample size $n$ and every sample:
--   $$\bar R_{\pi_0}(\pi; \mathcal W^\Gamma) = \sum_{t=0}^{m-1} \sup_{W \in \bar{\mathcal W}^\Gamma(\pi)} R^{(t)}_{\pi_0}(\pi; W), \qquad \hat{\bar R}_{\pi_0}(\pi; \mathcal W^\Gamma_n) = \sum_{t=0}^{m-1} \sup_{W \in \bar{\mathcal W}^\Gamma_n(\pi)} \hat R^{(t)}_{\pi_0}(\pi; W).$$
--   Here $\bar{\mathcal W}^\Gamma(\pi)$ consists of the weights $a^\Gamma_t(x) + u(y(\pi(t\mid x) - \pi_0(t\mid x)))(b^\Gamma_t(x) - a^\Gamma_t(x))$ with $u : \mathbb R \to [0,1]$ nondecreasing, and $\bar{\mathcal W}^\Gamma_n(\pi)$ is its restriction to the data.
--
--   The result replaces a supremum over an infinite-dimensional box of weight functions by one over a class of monotone, threshold-like weights indexed by the score $y(\pi(t\mid x) - \pi_0(t\mid x))$. It is the first step of the uniform-convergence argument behind Theorem 6 and Corollary 7.
--
--   **Formalization Note** The page states the result "for any $\pi : \mathcal X \to \Delta^m$"; Lean takes $\pi$ measurable. The supremum on each side of the sample identity is taken separately for each treatment, as on the page, so each $t$ may use its own $u$. The paper's appendix argument assumes no ties among the outcomes; the statement does not need it and is posed without it.
-- source:
--   Kallus & Zhou, arXiv:1805.08593v3, Proposition 3, pp. 14–15 (proof: Appendix A, pp. 35–36)

import Mathlib
import Definitions.Def_ConfoundRobust_Minimax_Setting

open MeasureTheory

namespace ConfoundRobust.Minimax

theorem proposition_3 {𝒳 : Type} [MeasurableSpace 𝒳] (m : ℕ) (hm : 2 ≤ m)
    (μ : Measure (Obs 𝒳 m)) [IsProbabilityMeasure μ]
    (e : Fin m → 𝒳 → ℝ) (he : IsNominalPropensity μ e) (ν : ℝ) (hν : 0 < ν)
    (heν : ∀ t x, ν ≤ e t x) (he1 : ∀ t x, e t x ≤ 1)
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ᵐ z ∂μ, |z.2.2| ≤ B)
    (Γ : ℝ) (hΓ : 1 ≤ Γ)
    (π0 : 𝒳 → Fin m → ℝ) (hπ0 : IsPolicy π0)
    (π : 𝒳 → Fin m → ℝ) (hπ : IsPolicy π) :
    worstRegret μ π π0 (WSet Γ e) =
        ∑ t, sSup ((fun W => regretT μ π π0 W t) '' WbarSet Γ e π π0) ∧
      ∀ (n : ℕ) (ω : Fin n → Obs 𝒳 m),
        sWorstRegret ω π π0 (WSetN Γ e ω) =
          ∑ t, sSup ((fun w => sRegretT ω π π0 w t) '' WbarSetN Γ e π π0 ω) := by sorry

end ConfoundRobust.Minimax
