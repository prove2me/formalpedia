-- Prove2me | Theorems.Thm_FiniteEnergyPlane_energy_ge_of_almostComplex
-- name    : FiniteEnergyPlane.energy_ge_of_almostComplex
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-23T16:58:47.196144+00:00
-- url     : https://prove2.me/theorems/7d36a502-fa94-4745-b6d7-810577728194
-- title:
--   Energy lower bound $\int_U|Du|^2\ge cS^2$ for maps $\partial_t u=A\,\partial_s u$ with $A$ close to a complex structure
-- statement:
--   Let $F$ be a real inner product space and $\beta\in\mathbb R$. There are constants $c>0$ and $\kappa>0$, depending only on $\beta$, with the following property.
--
--   Let $J_0:F\to F$ be a continuous linear map with $J_0^2=-1$ and $\|J_0\|\le\beta$. Let $\Lambda\ge0$ and $S>0$ with $\Lambda S\le\kappa$, let $q\in F$, $U\subseteq\mathbb C$ open, $u:\mathbb C\to F$ of class $C^2$ on $U$ and $A:\mathbb C\to L(F,F)$. Assume:
--   - at every $z\in U$ with $\|u(z)-q\|<S$: $\partial_tu(z)=A(z)\,\partial_su(z)$ and $\|A(z)-J_0\|\le\Lambda\|u(z)-q\|$;
--   - the sets $\{z\in U:\|u(z)-q\|\le\rho\}$ are compact for every $\rho<S$;
--   - there is $z_1\in U$ with $u(z_1)=q$ and $Du(z_1)\ne0$.
--
--   Then
--   $$\int_U\|Du(z)\|^2\,dz\ \ge\ c\,S^2 .$$
--
--   **Role.** This is the monotonicity lemma for pseudoholomorphic curves in a linear model: a curve through the centre of a ball of radius $S$, proper in that ball, has energy at least $cS^2$, uniformly when the almost complex structure along the curve is Lipschitz-close to a fixed complex structure.
--
--   **Formalization Note.** $\partial_su=Du(z)\,1$, $\partial_tu=Du(z)\,i$, $\|Du(z)\|$ is the operator norm of the real derivative, and the integral is the lower Lebesgue integral of $\|Du\|^2$ over $U$ (as an extended nonnegative real). The constants are chosen before $J_0$ and depend on $\beta$ only.
-- source:
--   A. Zinger, Notes on J-holomorphic maps, arXiv:1706.00331, Proposition 3.12; C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, p. 152

import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.Complex.ExponentialBounds

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal

/-- Monotonicity lemma near a complex structure on a real inner product space. Let `J₀` be a
complex structure with `‖J₀‖ ≤ β`. There are `c, κ > 0` (depending only on `β`) such that the
following holds. Let `Λ ≥ 0`, `S > 0` with `Λ S ≤ κ`, `q ∈ F`, `U ⊆ ℂ` open and `u` a `C²` map on
`U` with `∂ₜu = A(z) ∂ₛu` and `‖A(z) - J₀‖ ≤ Λ ‖u z - q‖` wherever `‖u z - q‖ < S`. Assume the sets
`{z ∈ U | ‖u z - q‖ ≤ ρ}` are compact for `ρ < S`, and `u z₁ = q`, `Du(z₁) ≠ 0` for some
`z₁ ∈ U`. Then `∫_U ‖Du‖² ≥ c S²`. -/
theorem energy_ge_of_almostComplex {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (β : ℝ) :
    ∃ c > 0, ∃ κ > 0, ∀ J₀ : F →L[ℝ] F, J₀.comp J₀ = -ContinuousLinearMap.id ℝ F → ‖J₀‖ ≤ β →
      ∀ Λ S : ℝ, 0 ≤ Λ → 0 < S → Λ * S ≤ κ →
      ∀ (q : F) (U : Set ℂ) (u : ℂ → F) (A : ℂ → F →L[ℝ] F), IsOpen U → ContDiffOn ℝ 2 u U →
      (∀ z ∈ U, ‖u z - q‖ < S → fderiv ℝ u z Complex.I = A z (fderiv ℝ u z 1) ∧
        ‖A z - J₀‖ ≤ Λ * ‖u z - q‖) →
      (∀ ρ, ρ < S → IsCompact {z | z ∈ U ∧ ‖u z - q‖ ≤ ρ}) →
      (∃ z₁ ∈ U, u z₁ = q ∧ fderiv ℝ u z₁ ≠ 0) →
      ENNReal.ofReal (c * S ^ 2) ≤ ∫⁻ z in U, ENNReal.ofReal (‖fderiv ℝ u z‖ ^ 2) := by
  sorry

end FiniteEnergyPlane
