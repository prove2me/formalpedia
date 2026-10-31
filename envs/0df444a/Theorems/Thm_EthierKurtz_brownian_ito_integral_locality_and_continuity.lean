-- Prove2me | Theorems.Thm_EthierKurtz_brownian_ito_integral_locality_and_continuity
-- name    : EthierKurtz.brownian_ito_integral_locality_and_continuity
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-31T03:50:54.053401+00:00
-- url     : https://prove2.me/theorems/1c98c8e0-c45c-4ef8-8a0e-16602ac22bfe
-- title:
--   Itô integrals against Brownian motion: locality, $L^2$ difference bound, continuous version and the maximal inequality
-- statement:
--   Let $W$ be a standard $d$-dimensional Brownian motion with completed natural filtration $(\mathcal F_t)$, and write $J=\int H\,dW^j$ for an Itô integral process of a continuous adapted integrand $H$. Then
--
--   $$\text{(i) if } H=H' \text{ on } E \text{ at all dyadic times } i s/2^N\le s, \text{ then } J_s=J'_s \text{ a.s. on } E;\qquad \text{(ii) } \mathbb E(J_t-J^1_t)^2\le \mathbb E\int_0^t (H_u-H^1_u)^2\,du \ \text{ for bounded } H,H^1;$$
--
--   $$\text{(iii) every bounded } H \text{ has an adapted Itô integral } J^c \text{ with continuous paths and } J^c_0=0;\qquad \text{(iv) } \lambda^2\,\mathbb P\Big(\sup_{t\le N}|J_t-J^1_t|>\lambda\Big)\le 2dN\beta$$
--
--   for continuous versions $J,J^1$ of bounded integrands with $\mathbb E(H_s-H^1_s)^2\le\beta$ for $s\le N$.
--
--   Role: the properties of the stochastic integral (locality, isometry for differences, continuous modification and Doob's maximal inequality) used by the Picard iteration, the localization of solutions, pathwise uniqueness and the face-invariance and moment arguments for the stochastic Kolmogorov system.
--
--   **Formalization Note**: part (iv) is stated with the constant $2dN\beta$ produced by the proof; Doob's $L^2$ maximal inequality gives the sharper $N\beta$, so (iv) is a weaker form of it, sufficient for every use. Part (i) is stated with agreement at the dyadic times $is/2^N$, $0\le i\le 2^N$, which for continuous integrands is agreement on $[0,s]$.
-- source:
--   I. Karatzas, S. E. Shreve, Brownian Motion and Stochastic Calculus, 2nd ed., Springer GTM 113, 1991, https://doi.org/10.1007/978-1-4612-0949-2, Section 3.2 (construction of the stochastic integral; Proposition 3.2.10: continuous martingale version and isometry; locality of the integral) and Theorem 1.3.8(iv) (Doob's maximal inequality)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_completedBrownianPast
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace EthierKurtz

theorem brownian_ito_integral_locality_and_continuity {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d) :
    (∀ (j : Fin d) (H H' J J' : ℝ≥0 → Ω → ℝ),
      (∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s)) →
      (∀ ω, Continuous fun s => H s ω) →
      (∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H' s)) →
      (∀ ω, Continuous fun s => H' s ω) →
      HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
        (fun s ω => W s ω j) H J →
      HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
        (fun s ω => W s ω j) H' J' →
      ∀ (s : ℝ≥0) (E : Set Ω),
      (∀ ω ∈ E, ∀ N i : ℕ, i ≤ 2 ^ N →
        H ((i : ℝ≥0) * s / 2 ^ N) ω = H' ((i : ℝ≥0) * s / 2 ^ N) ω) →
      ∀ᵐ ω ∂P, ω ∈ E → J s ω = J' s ω) ∧
    (∀ [IsProbabilityMeasure P] (j : Fin d) (H J H₁ J₁ : ℝ≥0 → Ω → ℝ),
      (∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s)) →
      (∀ ω, Continuous fun s => H s ω) → ∀ C : ℝ, (∀ s ω, |H s ω| ≤ C) →
      HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
        (fun s ω => W s ω j) H J →
      (∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H₁ s)) →
      (∀ ω, Continuous fun s => H₁ s ω) → (∀ s ω, |H₁ s ω| ≤ C) →
      HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
        (fun s ω => W s ω j) H₁ J₁ →
      ∀ t : ℝ≥0, ∫ ω, (J t ω - J₁ t ω) ^ 2 ∂P ≤
        ∫ ω, (∫ u in (0 : ℝ)..t.val, (H u.toNNReal ω - H₁ u.toNNReal ω) ^ 2) ∂P) ∧
    (∀ [IsProbabilityMeasure P] (j : Fin d) (H : ℝ≥0 → Ω → ℝ),
      (∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s)) →
      (∀ s, Measurable (H s)) → (∀ ω, Continuous fun s => H s ω) →
      ∀ C : ℝ, (∀ s ω, |H s ω| ≤ C) →
      ∃ Jc : ℝ≥0 → Ω → ℝ, (∀ ω, Continuous fun t => Jc t ω) ∧
        (∀ t, Measurable[completedBrownianPast P W (fun _ => x₀) t] (Jc t)) ∧
        (∀ t, Measurable (Jc t)) ∧ (∀ ω, Jc 0 ω = 0) ∧
        HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
          (fun s ω => W s ω j) H Jc) ∧
    (∀ [IsProbabilityMeasure P] (j : Fin d) (H H₁ J J₁ : ℝ≥0 → Ω → ℝ),
      (∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s)) →
      (∀ s, Measurable (H s)) → (∀ ω, Continuous fun s => H s ω) →
      ∀ C : ℝ, (∀ s ω, |H s ω| ≤ C) →
      (∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H₁ s)) →
      (∀ s, Measurable (H₁ s)) → (∀ ω, Continuous fun s => H₁ s ω) →
      ∀ C₁ : ℝ, (∀ s ω, |H₁ s ω| ≤ C₁) →
      HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
        (fun s ω => W s ω j) H J →
      HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
        (fun s ω => W s ω j) H₁ J₁ →
      (∀ ω, Continuous fun t => J t ω) → (∀ ω, Continuous fun t => J₁ t ω) →
      ∀ (N : ℕ) (β : ℝ), (∀ s : ℝ≥0, s ≤ N → ∫ ω, (H s ω - H₁ s ω) ^ 2 ∂P ≤ β) →
      ∀ lam : ℝ, 0 < lam →
      lam ^ 2 * P.real {ω | ∃ t : ℝ≥0, t ≤ N ∧ lam < |J t ω - J₁ t ω|} ≤ 2 * d * N * β) := by sorry

end EthierKurtz
