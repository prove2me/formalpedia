-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_norm_mul_fderiv_le_of_energy_lt_top
-- name    : FiniteEnergyPlane.exists_norm_mul_fderiv_le_of_energy_lt_top
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-24T18:22:45.058079+00:00
-- url     : https://prove2.me/theorems/9174e0af-2855-4bf9-8893-c1586f01cfb2
-- title:
--   Gradient bound near a finite-energy puncture of a pseudoholomorphic map
-- statement:
--   Let $E$ be a finite-dimensional real normed space, $J$ a smooth almost complex structure on an open set $O\subseteq E$, and $K\subseteq O$ compact. Let $D\subset\mathbb{C}$ be the open unit disc and $u$ a $C^\infty$ $J$-holomorphic map on $D\setminus\{0\}$ with $u(D\setminus\{0\})\subseteq K$ and
--   $$\int_{D\setminus\{0\}}\|Du(z)\|^2\,dz<\infty.$$
--   Then there are $r>0$ and $C$ such that
--   $$|z|\,\|Du(z)\|\le C\qquad\text{for all } 0<|z|<r .$$
--
--   In cylindrical coordinates $z=e^{-2\pi(s+it)}$ this says that the derivative of $u$ is bounded on a half-cylinder end. It is the gradient bound used to show that a finite-energy puncture is removable.
--
--   **Formalization Note** The energy is a lower integral in `ℝ≥0∞` of the squared operator norm of `fderiv ℝ u`. The conclusion is `∃ r > 0, ∃ C, ∀ z ≠ 0, ‖z‖ < r → ‖z‖ * ‖fderiv ℝ u z‖ ≤ C`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, Lemma 9.3, p. 153

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Gradient bound at a puncture (Wendl, Lemma 9.3, in disc coordinates). Let `J` be a smooth
almost complex structure on an open set `O ⊆ E` and `K ⊆ O` compact. A smooth `J`-holomorphic map on
the punctured unit disc with values in `K` and finite Dirichlet energy `∫ ‖Du‖²` satisfies
`|z| ‖Du(z)‖ ≤ C` for all `z ≠ 0` in some disc about the puncture. -/
theorem exists_norm_mul_fderiv_le_of_energy_lt_top {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (J : E → E →L[ℝ] E) (O : Set E)
    (hJ : JHolomorphic.IsAlmostComplexOn J O) (K : Set E) (hK : IsCompact K) (hKO : K ⊆ O)
    (u : ℂ → E) (hu : ContDiffOn ℝ ∞ u (ball 0 1 \ {0}))
    (hhol : JHolomorphic.IsJHolomorphicOn J (ball 0 1 \ {0}) u)
    (hmaps : Set.MapsTo u (ball 0 1 \ {0}) K)
    (hE : ∫⁻ z in ball 0 1 \ {0}, ENNReal.ofReal (‖fderiv ℝ u z‖ ^ 2) < ⊤) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, ∀ z : ℂ, z ≠ 0 → ‖z‖ < r → ‖z‖ * ‖fderiv ℝ u z‖ ≤ C := by
  sorry

end FiniteEnergyPlane
