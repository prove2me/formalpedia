-- Prove2me | Theorems.Thm_BurkholderDFI_Brownian_lemma_7_1
-- name    : BurkholderDFI.Brownian.lemma_7_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:11:25.477562+00:00
-- url     : https://prove2.me/theorems/7361ef25-6f37-49e1-a47a-a5ec27541dae
-- title:
--   Lemma 7.1 — a good-λ inequality P(g > βλ, f ≤ δλ) ≤ εP(g > λ) gives EΦ(g) ≤ γη/(1 − γε)·EΦ(f)
-- statement:
--   Let $\Phi:[0,\infty]\to[0,\infty]$ be non-decreasing and continuous with $\Phi(0)=0$ and $\Phi(2\lambda)\le c\,\Phi(\lambda)$. Let $f,g$ be nonnegative measurable functions on a probability space $(\Omega,\mathcal A,P)$, and let $\beta>1$, $\delta>0$, $\varepsilon>0$ be real numbers such that
--   $$P(g>\beta\lambda,\ f\le\delta\lambda)\le\varepsilon\,P(g>\lambda),\qquad\lambda>0. \tag{7.1}$$
--   Let $\gamma,\eta\ge0$ be real numbers with
--   $$\Phi(\beta\lambda)\le\gamma\,\Phi(\lambda),\qquad\Phi(\delta^{-1}\lambda)\le\eta\,\Phi(\lambda),\qquad\lambda>0, \tag{7.2}$$
--   and suppose $\gamma\varepsilon<1$. Then
--   $$E\Phi(g)\le\frac{\gamma\eta}{1-\gamma\varepsilon}\,E\Phi(f). \tag{7.3}$$
--
--   This lemma converts a distribution function ("good-$\lambda$") inequality between two random variables into an integral inequality for every $\Phi$ of moderate growth. It is the bridge from Theorem 6.2 to Theorem 6.1, and is reused throughout the paper.
--
--   **Formalization Note** $f$ and $g$ may take the value $+\infty$ (needed when $g$ is a square or maximal function); the paper's "nonnegative measurable functions" are the finite-valued case, so this is a strengthening that the paper's truncation argument ($g\wedge n$) covers. $\gamma,\eta$ are taken nonnegative: if $\Phi\not\equiv0$, (7.2) forces $\gamma,\eta\ge1$, and if $\Phi\equiv0$ the conclusion is trivial. The paper's exclusion of $\Phi\equiv0$ is dropped for the same reason. Expectations are integrals in $[0,\infty]$.
-- source:
--   Burkholder, Distribution Function Inequalities for Martingales, Ann. Probability 1 (1973), Lemma 7.1, p. 26

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace BurkholderDFI.Brownian

/-- Lemma 7.1, p. 26: the good-λ lemma. `f, g` are `[0, ∞]`-valued. -/
theorem lemma_7_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Φ : ℝ≥0∞ → ℝ≥0∞) (c : ℝ≥0) (hΦ : BurkholderDFI.SquareFnLp.IsPhi Φ c)
    (f g : Ω → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g)
    (β δ ε : ℝ) (hβ : 1 < β) (hδ : 0 < δ) (hε : 0 < ε)
    (h71 : ∀ l : ℝ, 0 < l →
      P {ω | ENNReal.ofReal (β * l) < g ω ∧ f ω ≤ ENNReal.ofReal (δ * l)}
        ≤ ENNReal.ofReal ε * P {ω | ENNReal.ofReal l < g ω})
    (γ η : ℝ≥0)
    (h72 : ∀ l : ℝ, 0 < l →
      Φ (ENNReal.ofReal (β * l)) ≤ γ * Φ (ENNReal.ofReal l) ∧
      Φ (ENNReal.ofReal (δ⁻¹ * l)) ≤ η * Φ (ENNReal.ofReal l))
    (hγε : (γ : ℝ) * ε < 1) :
    ∫⁻ ω, Φ (g ω) ∂P ≤ ENNReal.ofReal (γ * η / (1 - γ * ε)) * ∫⁻ ω, Φ (f ω) ∂P := by sorry

end BurkholderDFI.Brownian
