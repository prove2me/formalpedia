-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_tendsto_of_energy_lt_top
-- name    : FiniteEnergyPlane.exists_tendsto_of_energy_lt_top
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-24T18:22:46.132454+00:00
-- url     : https://prove2.me/theorems/a429fb1d-4cf9-4be9-a343-ea799b3616c3
-- title:
--   Limit at a finite-energy puncture of a pseudoholomorphic map
-- statement:
--   Let $E$ be a finite-dimensional real normed space, $J$ a smooth almost complex structure on an open set $O\subseteq E$, and $K\subseteq O$ compact. Let $D\subset\mathbb{C}$ be the open unit disc and $u$ a $C^\infty$ $J$-holomorphic map on $D\setminus\{0\}$ with $u(D\setminus\{0\})\subseteq K$,
--   $$\int_{D\setminus\{0\}}\|Du(z)\|^2\,dz<\infty,$$
--   and assume there are $r>0$ and $C$ with $|z|\,\|Du(z)\|\le C$ for $0<|z|<r$. Then $u(z)$ converges as $z\to 0$: there is $x_0\in E$ with $u(z)\to x_0$ as $z\to0$, $z\ne0$.
--
--   This is the continuity part of the removable singularity theorem: a finite-energy puncture with the stated gradient bound has a continuous extension.
--
--   **Formalization Note** The energy is a lower integral in `ℝ≥0∞` of the squared operator norm of `fderiv ℝ u`. The limit is `Tendsto u (𝓝[≠] 0) (𝓝 x₀)`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, Theorem 9.2 and (9.1), pp. 152-155

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Limit at a puncture (Wendl, Theorem 9.2, continuity part, (9.1)). Let `J` be a smooth almost
complex structure on an open set `O ⊆ E` and `K ⊆ O` compact. A smooth `J`-holomorphic map on the
punctured unit disc with values in `K`, finite Dirichlet energy `∫ ‖Du‖²` and `|z| ‖Du(z)‖` bounded
near the puncture has a limit at the puncture. -/
theorem exists_tendsto_of_energy_lt_top {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (J : E → E →L[ℝ] E) (O : Set E)
    (hJ : JHolomorphic.IsAlmostComplexOn J O) (K : Set E) (hK : IsCompact K) (hKO : K ⊆ O)
    (u : ℂ → E) (hu : ContDiffOn ℝ ∞ u (ball 0 1 \ {0}))
    (hhol : JHolomorphic.IsJHolomorphicOn J (ball 0 1 \ {0}) u)
    (hmaps : Set.MapsTo u (ball 0 1 \ {0}) K)
    (hE : ∫⁻ z in ball 0 1 \ {0}, ENNReal.ofReal (‖fderiv ℝ u z‖ ^ 2) < ⊤)
    (hG : ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, ∀ z : ℂ, z ≠ 0 → ‖z‖ < r → ‖z‖ * ‖fderiv ℝ u z‖ ≤ C) :
    ∃ x₀ : E, Tendsto u (𝓝[≠] 0) (𝓝 x₀) := by
  sorry

end FiniteEnergyPlane
