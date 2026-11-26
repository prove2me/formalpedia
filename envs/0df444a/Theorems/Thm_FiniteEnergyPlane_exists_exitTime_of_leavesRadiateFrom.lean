-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_exitTime_of_leavesRadiateFrom
-- name    : FiniteEnergyPlane.exists_exitTime_of_leavesRadiateFrom
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-26T21:37:53.096788+00:00
-- url     : https://prove2.me/theorems/261f906c-2f5a-46ba-934a-756c6f01de3b
-- title:
--   Exit times of the characteristic leaves of a disk
-- statement:
--   Let $e : \mathbb{C} \to V_1$ be smooth, let $z_0$ lie in the open unit disk with $\mathtt{charField}\ e\ z_0 = 0$, assume every characteristic leaf of the closed unit disk issues from $z_0$ and reaches the unit circle (`LeavesRadiateFrom e z₀`), and assume $e^*\lambda_0(iz) > 0$ at every point $z$ of the unit circle. Let $X$ be a smooth compactly supported vector field on $\mathbb{C}$ that agrees with the characteristic field on the disk of radius $2$, and let $\psi$ be a continuous flow of $X$ ($\psi_0 = \mathrm{id}$, $\partial_s\psi_s(y) = X(\psi_s y)$).
--
--   Then there is an exit time $b$, continuous on the closed unit disk minus $z_0$, such that for every such $z$:
--   - $b(z) \ge 0$;
--   - $\psi_s z$ lies in the open unit disk for $s < b(z)$, on the unit circle for $s = b(z)$, and outside the closed unit disk for $s > b(z)$;
--   - $\psi_s z \to z_0$ as $s \to -\infty$;
--   - $\psi_s z \ne z_0$ for all $s$.
--
--   Role: the exit time and the exit point $\psi_{b(z)}z$ parametrize the leaves of the disk by points of the unit circle.
-- source:
--   Elementary lemma in the setting of U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), § 3.2

import Definitions.Def_FiniteEnergyPlane_SpanningDisk

namespace FiniteEnergyPlane

open Metric Filter Topology
open scoped ContDiff

/-- Exit times of the characteristic leaves of a disk. Let `e : ℂ → V 1` be smooth, with
characteristic field vanishing at `z₀` in the open unit disk, every leaf of the closed unit disk
issuing from `z₀` and reaching the unit circle, and `e*λ₀(i z) > 0` on the unit circle. Let `ψ` be
the flow of a smooth compactly supported vector field `X` on `ℂ` that agrees with the characteristic
field on the disk of radius `2`. Then there is an exit time `b`, continuous on the closed unit disk
minus `z₀`, such that for every such `z`: `b z ≥ 0`; `ψ_s z` lies in the open unit disk for
`s < b z`, on the unit circle for `s = b z`, and outside the closed unit disk for `s > b z`;
`ψ_s z → z₀` as `s → -∞`; and `ψ_s z ≠ z₀` for all `s`. -/
theorem exists_exitTime_of_leavesRadiateFrom (e : ℂ → V 1) (he : ContDiff ℝ ∞ e) (z₀ : ℂ)
    (hz₀ : z₀ ∈ ball (0 : ℂ) 1) (hV : charField e z₀ = 0) (hL : LeavesRadiateFrom e z₀)
    (hS : ∀ z ∈ sphere (0 : ℂ) 1, 0 < liouville (e z) (fderiv ℝ e z (Complex.I * z)))
    (X : ℂ → ℂ) (hX : ContDiff ℝ ∞ X) (hXK : HasCompactSupport X)
    (hXV : ∀ z ∈ ball (0 : ℂ) 2, X z = charField e z)
    (ψ : ℝ → ℂ → ℂ) (hψ : Continuous (fun p : ℝ × ℂ => ψ p.1 p.2)) (hψ0 : ∀ y, ψ 0 y = y)
    (hψd : ∀ t y, HasDerivAt (fun s => ψ s y) (X (ψ t y)) t) :
    ∃ b : ℂ → ℝ, ContinuousOn b (closedBall (0 : ℂ) 1 \ {z₀}) ∧
      ∀ z ∈ closedBall (0 : ℂ) 1, z ≠ z₀ → 0 ≤ b z ∧ (∀ s < b z, ψ s z ∈ ball (0 : ℂ) 1) ∧
        ψ (b z) z ∈ sphere (0 : ℂ) 1 ∧ (∀ s, b z < s → ψ s z ∉ closedBall (0 : ℂ) 1) ∧
        Tendsto (fun s => ψ s z) atBot (𝓝 z₀) ∧ ∀ s, ψ s z ≠ z₀ := by
  sorry

end FiniteEnergyPlane
