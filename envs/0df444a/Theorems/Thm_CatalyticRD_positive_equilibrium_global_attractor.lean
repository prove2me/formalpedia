-- Prove2me | Theorems.Thm_CatalyticRD_positive_equilibrium_global_attractor
-- name    : CatalyticRD.positive_equilibrium_global_attractor
-- status  : Open
-- author  : @shivm
-- created : 2026-10-04T14:30:21.519185+00:00
-- url     : https://prove2.me/theorems/e8cbb555-b256-4546-a7ae-31ec188264e3
-- title:
--   Positive equilibrium attracts all positive solutions for $M_2\le M_1<2M_2$
-- statement:
--   **Conjecture (Nguyen–Tang; AIM problem 416).** Let $\Omega$ be a smooth bounded connected domain with $|\Omega|=1$, $d_1,d_2,d_3>0$, and $a_0,b_0,c_0$ admissible (strictly positive, $C^2$, Neumann). Let $(a,b,c)$ be a classical solution and $M_1=\int_\Omega(a_0+c_0)$, $M_2=\int_\Omega(b_0+c_0)$. If $M_2\le M_1<2M_2$, then $a\to\frac{M_1}2$, $b\to M_2-\frac{M_1}2$, $c\to\frac{M_1}2$ uniformly on $\Omega$ as $t\to\infty$.
--
--   Uniform convergence is the $L^\infty$ convergence of the source.
-- source:
--   T. L. Nguyen and B. Q. Tang, Stability analysis of irreversible chemical reaction-diffusion systems with boundary equilibria, Z. Angew. Math. Phys. 77 (2026), 199, https://doi.org/10.1007/s00033-026-02847-0, Conjecture after Table 1 (Section 1); AIM problem 416; AIM open problem 416 (github.com/MColbrook/AIM, problems/416-catalytic-reaction-diffusion-positive-attractor.md)

import Mathlib
import Definitions.Def_CatalyticRD_Setup

open MeasureTheory Set Filter Topology

namespace CatalyticRD

theorem positive_equilibrium_global_attractor {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hΩ : IsSmoothBoundedDomain Ω φ) (hvol : volume Ω = 1)
    (d₁ d₂ d₃ : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hd₃ : 0 < d₃)
    (a₀ b₀ c₀ : EuclideanSpace ℝ (Fin n) → ℝ)
    (ha₀ : IsAdmissibleDatum Ω φ a₀) (hb₀ : IsAdmissibleDatum Ω φ b₀)
    (hc₀ : IsAdmissibleDatum Ω φ c₀)
    (M₁ M₂ : ℝ) (hM₁ : M₁ = ∫ x in Ω, (a₀ x + c₀ x)) (hM₂ : M₂ = ∫ x in Ω, (b₀ x + c₀ x))
    (hM : M₂ ≤ M₁ ∧ M₁ < 2 * M₂)
    (a b c : ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hsol : IsClassicalSolution Ω φ d₁ d₂ d₃ a₀ b₀ c₀ a b c) :
    TendstoUniformlyOn a (fun _ => M₁ / 2) atTop Ω ∧
      TendstoUniformlyOn b (fun _ => M₂ - M₁ / 2) atTop Ω ∧
      TendstoUniformlyOn c (fun _ => M₁ / 2) atTop Ω := by sorry

end CatalyticRD
