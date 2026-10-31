-- Prove2me | Theorems.Thm_EthierKurtz_brownian_ito_integral_and_formula
-- name    : EthierKurtz.brownian_ito_integral_and_formula
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-30T18:08:48.488105+00:00
-- url     : https://prove2.me/theorems/1558a108-3a0d-44bb-bdc8-5d99eebf483a
-- title:
--   Itô integrals against Brownian motion: existence, $L^2$ bound and mean zero, and the multidimensional Itô formula
-- statement:
--   Let $W$ be a standard $d$-dimensional Brownian motion with completed natural filtration $(\mathcal F_t)$. Then
--
--   $$\text{(i) } J_t=\int_0^t H_s\,dW^j_s \text{ exists for every continuous adapted } H;\quad \text{(ii) } |H|\le C \Rightarrow J_t\in L^2,\ \mathbb E J_t^2\le C^2 t,\ \mathbb E J_t=0;$$
--
--   $$\text{(iii) } f(X_t)=f(X_0)+\sum_{i,j}\int_0^t \partial_i f(X_u)H_{ij}(u)\,dW^j_u+\sum_i\int_0^t\partial_i f(X_u)b_i(u)\,du+\tfrac12\sum_{i,i',j}\int_0^t\partial_{ii'}f(X_u)H_{ij}H_{i'j}\,du$$
--
--   a.s. for every $f\in C^2$ and every continuous adapted Itô process $X_t=X_0+\sum_j\int_0^t H_{\cdot j}\,dW^j+\int_0^t b\,du$ with continuous adapted $H,b$.
--
--   Role: the stochastic-calculus toolkit (existence of the Itô integral, isometry bound and Itô's rule) used by every later step of the Markov-property proof for the stochastic Kolmogorov system.
-- source:
--   I. Karatzas, S. E. Shreve, Brownian Motion and Stochastic Calculus, 2nd ed., Springer GTM 113, 1991, https://doi.org/10.1007/978-1-4612-0949-2, Section 3.2 (construction and properties of the stochastic integral) and Theorem 3.3.6 (Itô's rule, d-dimensional)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_completedBrownianPast
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace EthierKurtz

theorem brownian_ito_integral_and_formula {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω}
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d) :
    (∀ (j : Fin d) (H : ℝ≥0 → Ω → ℝ),
      (∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s)) →
      (∀ ω, Continuous fun s => H s ω) →
      ∃ J : ℝ≥0 → Ω → ℝ, HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
        (fun s ω => W s ω j) H J) ∧
    (∀ [IsProbabilityMeasure P] (j : Fin d) (H J : ℝ≥0 → Ω → ℝ),
      (∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s)) →
      (∀ ω, Continuous fun s => H s ω) → ∀ C : ℝ, (∀ s ω, |H s ω| ≤ C) →
      HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
        (fun s ω => W s ω j) H J → ∀ t : ℝ≥0,
      MemLp (J t) 2 P ∧ ∫ ω, J t ω ^ 2 ∂P ≤ C ^ 2 * t ∧ ∫ ω, J t ω ∂P = 0) ∧
    (∀ [IsFiniteMeasure P] (e : ℕ) (X : ℝ≥0 → Ω → SDEState e),
      (∀ s, Measurable (X s)) → (∀ ω, Continuous fun s => X s ω) →
      (∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (X s)) →
      ∀ (H J : Fin e → Fin d → ℝ≥0 → Ω → ℝ) (b : Fin e → ℝ≥0 → Ω → ℝ),
      (∀ i j s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H i j s)) →
      (∀ i j ω, Continuous fun s => H i j s ω) →
      (∀ i j, HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
        (fun s ω => W s ω j) (H i j) (J i j)) →
      (∀ i s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (b i s)) →
      (∀ i ω, Continuous fun s => b i s ω) →
      (∀ᵐ ω ∂P, ∀ (s : ℝ≥0) (i : Fin e), X s ω i = X 0 ω i + (∑ j, J i j s ω) +
        ∫ u in (0 : ℝ)..s.val, b i u.toNNReal ω) →
      ∀ (f : SDEState e → ℝ), ContDiff ℝ 2 f → ∀ (K : Fin e → Fin d → ℝ≥0 → Ω → ℝ),
      (∀ i j, HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
        (fun s ω => W s ω j)
        (fun s ω => fderiv ℝ f (X s ω) (EuclideanSpace.single i 1) * H i j s ω) (K i j)) →
      ∀ t : ℝ≥0,
      ∀ᵐ ω ∂P, f (X t ω) = f (X 0 ω) + (∑ i, ∑ j, K i j t ω) +
        (∑ i, ∫ u in (0 : ℝ)..t.val,
          fderiv ℝ f (X u.toNNReal ω) (EuclideanSpace.single i 1) * b i u.toNNReal ω) +
        (1 / 2) * ∑ i, ∑ i', ∑ j, ∫ u in (0 : ℝ)..t.val,
          fderiv ℝ (fderiv ℝ f) (X u.toNNReal ω) (EuclideanSpace.single i 1)
            (EuclideanSpace.single i' 1) * H i j u.toNNReal ω * H i' j u.toNNReal ω) := by sorry

end EthierKurtz
