-- Prove2me | Theorems.Thm_FastRatesSVM_Rates_theorem_2_8
-- name    : FastRatesSVM.Rates.theorem_2_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:59:02.029072+00:00
-- url     : https://prove2.me/theorems/ad4d7e21-cb41-44a9-86ce-1d47501e10ab
-- title:
--   Theorem 2.8 — fast classification rate for Gaussian SVMs without offset
-- statement:
--   Let $X$ be the closed unit ball in $\mathbb R^d$, with $d>0$, and let $P$ be a distribution on $X\times\{-1,1\}$ with Tsybakov exponent $q\in[0,\infty]$ and finite geometric noise exponent $\alpha>0$. Define $\beta,\lambda_n,\sigma_n$ as in Theorem 2.8. For every $\varepsilon>0$ there is a constant $C>0$, chosen before $x$ and $n$, such that for every $x\ge1$ and $n\ge1$,
--   $$
--   \Pr^*\!\left\{T:
--     R_P(f_{T,\lambda_n})\le R_P+C x^2 n^{-\beta+\varepsilon}
--     \text{ for every SVM minimizer }f_{T,\lambda_n}\right\}
--     \ge1-e^{-x}.
--   $$
--
--   The theorem gives a classification excess-risk rate under separate label and geometric noise conditions. **Formalization Note** The event also asserts existence of an empirical minimizer, as stated in the paper's SVM setup, so the universal claim is nonvacuous. The regression function is a fixed measurable version of the conditional label probability. $\tau_x$ uses distance zero to an empty set. $\Pr^*$ is the product measure's outer measure of the event, with no measurability guard. The $\alpha=\infty$ and offset clauses are outside this mission.
-- source:
--   Steinwart, Scovel, Fast Rates for Support Vector Machines Using Gaussian Kernels, arXiv:0708.1838v1, p. 9, Theorem 2.8, finite-alpha/no-offset clause

import Definitions.Def_FastRatesSVM_Rates_Parameters

open MeasureTheory

namespace FastRatesSVM.Rates

/-- Theorem 2.8, finite geometric noise exponent and the SVM without offset,
arXiv:0708.1838v1, p. 9. The event includes existence of a minimizer. -/
theorem theorem_2_8 (d : ℕ) (hd : 0 < d) (D : BinaryDistribution d)
    (q : ENNReal) (hq : TsybakovNoise D q) (α : ℝ)
    (hgeo : GeometricNoise D α) :
    ∀ (ε : ℝ), 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (x : ℝ), 1 ≤ x → ∀ (n : ℕ), 1 ≤ n →
        ENNReal.ofReal (1 - Real.exp (-x)) ≤
          (Measure.pi fun _ : Fin n => jointLaw D)
            {T : Fin n → E d × ℝ |
              (∀ i, (T i).1 ∈ X d ∧ ((T i).2 = 1 ∨ (T i).2 = -1)) ∧
              (∃ f : E d → ℝ, IsSVMSol (sigmaN d α q n) (lambdaN α q n) T f) ∧
              (∀ f : E d → ℝ,
                IsSVMSol (sigmaN d α q n) (lambdaN α q n) T f →
                  classRisk D f ≤ bayesClassRisk D +
                    ENNReal.ofReal (C * x ^ 2 * (n : ℝ) ^ (-beta α q + ε)))} := by sorry

end FastRatesSVM.Rates
