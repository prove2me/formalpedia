-- Prove2me | Theorems.Thm_FiniteEnergyPlane_tendsto_norm_mul_fderiv_of_energy_lt_top
-- name    : FiniteEnergyPlane.tendsto_norm_mul_fderiv_of_energy_lt_top
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-24T21:15:04.549122+00:00
-- url     : https://prove2.me/theorems/21c589e4-18ed-433e-9fa6-9d2cb940eaf8
-- title:
--   Decay of the weighted gradient at a finite-energy puncture of a pseudoholomorphic map
-- statement:
--   Let $E$ be a finite-dimensional real normed space, $J$ a smooth almost complex structure on an open set $O\subseteq E$ (so $J(x)^2=-1$ for $x\in O$), and $K\subseteq O$ compact. Let $D\subset\mathbb{C}$ be the open unit disc and $u$ a map that is $C^\infty$ and $J$-holomorphic on $D\setminus\{0\}$, takes values in $K$ there, and satisfies
--   $$\int_{D\setminus\{0\}}\|Du(z)\|^2\,dz<\infty .$$
--   Assume moreover that there are $r>0$ and $C$ with $|z|\,\|Du(z)\|\le C$ for $0<|z|<r$. Then
--   $$|z|\,\|Du(z)\|\longrightarrow 0\qquad (z\to 0,\ z\neq 0).$$
--
--   In cylindrical coordinates $z=e^{-(s+it)}$ this says that the derivative of $u$ tends to zero uniformly along the end. It is used for the existence of a limit of $u$ at the puncture (Wendl, Theorem 9.2).
--
--   **Formalization Note** $\|Du(z)\|$ is the operator norm of `fderiv ℝ u z`; the energy is a lower integral in `ℝ≥0∞`. The convergence is `Tendsto (fun z => ‖z‖ * ‖fderiv ℝ u z‖) (𝓝[≠] 0) (𝓝 0)`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, proof of Theorem 9.2, pp. 154-155

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Decay of the weighted gradient at a puncture (Wendl, Theorem 9.2). Let `J` be a smooth almost
complex structure on an open set `O ⊆ E` and `K ⊆ O` compact. For a smooth `J`-holomorphic map on
the punctured unit disc with values in `K`, finite Dirichlet energy `∫ ‖Du‖²` and `|z| ‖Du(z)‖`
bounded near the puncture, `|z| ‖Du(z)‖ → 0` as `z → 0`. -/
theorem tendsto_norm_mul_fderiv_of_energy_lt_top {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (J : E → E →L[ℝ] E) (O : Set E)
    (hJ : JHolomorphic.IsAlmostComplexOn J O) (K : Set E) (hK : IsCompact K) (hKO : K ⊆ O)
    (u : ℂ → E) (hu : ContDiffOn ℝ ∞ u (ball 0 1 \ {0}))
    (hhol : JHolomorphic.IsJHolomorphicOn J (ball 0 1 \ {0}) u)
    (hmaps : Set.MapsTo u (ball 0 1 \ {0}) K)
    (hE : ∫⁻ z in ball 0 1 \ {0}, ENNReal.ofReal (‖fderiv ℝ u z‖ ^ 2) < ⊤)
    (hG : ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, ∀ z : ℂ, z ≠ 0 → ‖z‖ < r → ‖z‖ * ‖fderiv ℝ u z‖ ≤ C) :
    Tendsto (fun z : ℂ => ‖z‖ * ‖fderiv ℝ u z‖) (𝓝[≠] 0) (𝓝 0) := by
  sorry

end FiniteEnergyPlane
