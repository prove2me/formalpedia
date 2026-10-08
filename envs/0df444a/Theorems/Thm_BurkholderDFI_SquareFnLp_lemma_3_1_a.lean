-- Prove2me | Theorems.Thm_BurkholderDFI_SquareFnLp_lemma_3_1_a
-- name    : BurkholderDFI.SquareFnLp.lemma_3_1_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:54:28.353037+00:00
-- url     : https://prove2.me/theorems/66bbd86d-883d-4d00-b7eb-48bea3bd95c7
-- title:
--   Lemma 3.1, (3.4) — for Y = S_n(θf) ∨ f_n*, λP(Y > (1 + 2θ²)^{1/2}λ) ≤ 3∫_{Y>λ} f_n
-- statement:
--   Let $f = (f_1, f_2, \dots)$ be a nonnegative submartingale relative to $\mathcal A_1 \subseteq \mathcal A_2 \subseteq \cdots$, let $n$ be a positive integer, let $\theta > 0$, and put $\beta = (1 + 2\theta^2)^{1/2}$. Let
--   $$Y = S_n(\theta f) \vee f_n^*, \qquad S_n(\theta f) = \theta\Bigl(\sum_{k=1}^n d_k^2\Bigr)^{1/2}, \quad f_n^* = \max_{1 \le k \le n} |f_k| .$$
--   Then
--   $$\lambda\, P(Y > \beta\lambda) \le 3 \int_{\{Y > \lambda\}} f_n \, dP, \qquad \lambda > 0. \tag{3.4}$$
--
--   This is the distribution function inequality of the form (1.2) which, combined with (1.3), yields the moment bound (3.5) for nonnegative submartingales.
--
--   **Formalization Note** "Nonnegative" means $f_k \ge 0$ almost everywhere for $k \ge 1$; the integrand is $\max(f_n, 0)$, which equals $f_n$ almost everywhere. $\theta f$ is the process $(\theta f_1, \theta f_2, \dots)$. The Mathlib convention at index $0$ is as in (1.1). The paper states (3.4) and (3.5) as one lemma; they are split into two items.
-- source:
--   Burkholder, Distribution Function Inequalities for Martingales, Ann. Probability 1 (1973), Lemma 3.1, p. 22, display (3.4)

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

namespace BurkholderDFI.SquareFnLp

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

theorem lemma_3_1_a {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hsub : Submartingale f ℱ P) (hnn : ∀ n, 1 ≤ n → 0 ≤ᵐ[P] f n)
    (n : ℕ) (hn : 1 ≤ n) (θ : ℝ) (hθ : 0 < θ) (l : ℝ) (hl : 0 < l) :
    ENNReal.ofReal l * P {ω | ENNReal.ofReal (Real.sqrt (1 + 2 * θ ^ 2) * l)
        < max (sqFnN (fun k x => θ * f k x) n ω) (maxFnN f n ω)}
      ≤ 3 * ∫⁻ ω in {ω | ENNReal.ofReal l
          < max (sqFnN (fun k x => θ * f k x) n ω) (maxFnN f n ω)}, ENNReal.ofReal (f n ω) ∂P := by sorry

end BurkholderDFI.SquareFnLp
