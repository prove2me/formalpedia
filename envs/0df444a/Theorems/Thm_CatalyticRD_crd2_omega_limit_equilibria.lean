-- Prove2me | Theorems.Thm_CatalyticRD_crd2_omega_limit_equilibria
-- name    : CatalyticRD.crd2_omega_limit_equilibria
-- status  : Open
-- author  : @shivm
-- created : 2026-10-04T18:17:47.001461+00:00
-- url     : https://prove2.me/theorems/c3edd1f1-6994-4262-a0d3-ac3bef5db526
-- title:
--   ω-limit points of the catalytic system are constant equilibria
-- statement:
--   Let $\Omega=\{\varphi<0\}\subset\mathbb R^n$ be a smooth bounded connected domain with $|\Omega|=1$, $d_1,d_2,d_3>0$, and let $(a,b,c)$ be a classical solution of the catalytic system (Nguyen–Tang, eq. (1.1))
--
--   $$\partial_t a-d_1\Delta a=b(c-a),\quad \partial_t b-d_2\Delta b=b(c-a),\quad \partial_t c-d_3\Delta c=-b(c-a)$$
--
--   with homogeneous Neumann conditions and admissible initial data $a_0,b_0,c_0$ ($C^2(\overline\Omega)$, strictly positive on $\overline\Omega$, Neumann-compatible), all as in `CatalyticRD_Setup`. Then for every sequence $t_k\to\infty$ there are a subsequence $t_{k_j}$ and constants $\alpha,\beta,\gamma$ with
--
--   $$\beta(\gamma-\alpha)=0,\qquad (a,b,c)(t_{k_j},\cdot)\to(\alpha,\beta,\gamma)\ \text{ uniformly on }\Omega.$$
--
--   So the ω-limit set in $C(\overline\Omega)^3$ is nonempty and consists of spatially constant equilibria.
--
--   This lemma carries the core difficulty of the conjecture. It combines uniform-in-time $L^\infty$ bounds (Nguyen–Tang, Theorem 2.1), precompactness of the orbit in $C(\overline\Omega)^3$ (parabolic regularity), and the energy identity
--
--   $$\frac{d}{dt}\frac12\int_\Omega(a^2+c^2)=-d_1\int_\Omega|\nabla a|^2-d_3\int_\Omega|\nabla c|^2-\int_\Omega b(c-a)^2$$
--
--   with LaSalle's invariance principle. Nguyen–Tang carry out this argument only for $M_1\ge2M_2$ (Proposition 2.5, $L^2$ convergence); here it is needed for every mass ratio, where both the positive and the boundary equilibrium are possible limits.
-- source:
--   T. L. Nguyen and B. Q. Tang, Stability analysis of irreversible chemical reaction-diffusion systems with boundary equilibria, Z. Angew. Math. Phys. 77 (2026) 199, https://doi.org/10.1007/s00033-026-02847-0: Theorem 2.1 (uniform-in-time L^∞ bounds) and Proposition 2.5 with its proof (energy identity, convergence to equilibria); combined with the LaSalle invariance principle (D. Henry, Geometric Theory of Semilinear Parabolic Equations, LNM 840, Springer 1981, §4.3).

import Mathlib
import Definitions.Def_CatalyticRD_Setup

open MeasureTheory Set Filter Topology

namespace CatalyticRD

theorem crd2_omega_limit_equilibria {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hΩ : IsSmoothBoundedDomain Ω φ) (hvol : volume Ω = 1)
    (d₁ d₂ d₃ : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hd₃ : 0 < d₃)
    (a₀ b₀ c₀ : EuclideanSpace ℝ (Fin n) → ℝ)
    (ha₀ : IsAdmissibleDatum Ω φ a₀) (hb₀ : IsAdmissibleDatum Ω φ b₀)
    (hc₀ : IsAdmissibleDatum Ω φ c₀)
    (a b c : ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hsol : IsClassicalSolution Ω φ d₁ d₂ d₃ a₀ b₀ c₀ a b c) :
    ∀ u : ℕ → ℝ, Tendsto u atTop atTop → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∃ α β γ : ℝ, β * (γ - α) = 0 ∧
        TendstoUniformlyOn (fun k => a (u (ψ k))) (fun _ => α) atTop Ω ∧
        TendstoUniformlyOn (fun k => b (u (ψ k))) (fun _ => β) atTop Ω ∧
        TendstoUniformlyOn (fun k => c (u (ψ k))) (fun _ => γ) atTop Ω := by sorry

end CatalyticRD
