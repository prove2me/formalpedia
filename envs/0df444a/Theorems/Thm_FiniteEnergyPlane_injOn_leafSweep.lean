-- Prove2me | Theorems.Thm_FiniteEnergyPlane_injOn_leafSweep
-- name    : FiniteEnergyPlane.injOn_leafSweep
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-26T21:49:40.108552+00:00
-- url     : https://prove2.me/theorems/ccc67a59-fffc-5cd9-9cd3-a7cb1a39df04
-- title:
--   Injectivity of the leaf sweep of a transverse loop
-- statement:
--   Let $e : \mathbb{C} \to V_1$ be smooth, with characteristic field vanishing at $z_0$ in the open unit disk, every characteristic leaf of the closed unit disk issuing from $z_0$ and reaching the unit circle (`LeavesRadiateFrom e z₀`), and $e^*\lambda_0(iz) > 0$ on the unit circle. Let $X$ be a smooth compactly supported vector field on $\mathbb{C}$ agreeing with the characteristic field on the disk of radius $2$, and let $\psi$ be a jointly smooth flow of $X$. Let $c$ be a $C^1$ loop in the closed unit disk with winding number $1$ around $z_0$ that is transverse to the characteristic field: $e^*\lambda_0(c'(t)) \ne 0$ for all $t$.
--
--   Then the backward sweep $p \mapsto \psi_{\operatorname{Re} p}(c(\operatorname{Im} p))$ is injective on the half-strip $\{\operatorname{Re} p < 0,\ 0 \le \operatorname{Im} p < 1\}$.
--
--   Role: the sweep of a transverse loop along the leaves covers each point of the disk at most once.
-- source:
--   U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), § 3.2

import Definitions.Def_FiniteEnergyPlane_SpanningDisk

namespace FiniteEnergyPlane

open Metric Set
open scoped ContDiff

/-- Injectivity of the backward sweep of a transverse loop along the characteristic leaves. Let
`e : ℂ → V 1` be smooth, with characteristic field vanishing at `z₀` in the open unit disk, every leaf
of the closed unit disk issuing from `z₀` and reaching the unit circle, and `e*λ₀(i z) > 0` on the unit
circle. Let `ψ` be the jointly smooth flow of a smooth compactly supported vector field `X` on `ℂ` that
agrees with the characteristic field on the disk of radius `2`. Let `c` be a `C¹` loop in the closed
unit disk that winds once around `z₀` and is transverse to the characteristic field. Then
`p ↦ ψ_{re p}(c (im p))` is injective on the half-strip `{re < 0, 0 ≤ im < 1}`. -/
theorem injOn_leafSweep (e : ℂ → V 1) (he : ContDiff ℝ ∞ e) (z₀ : ℂ)
    (hz₀ : z₀ ∈ ball (0 : ℂ) 1) (hV : charField e z₀ = 0) (hL : LeavesRadiateFrom e z₀)
    (hS : ∀ z ∈ sphere (0 : ℂ) 1, 0 < liouville (e z) (fderiv ℝ e z (Complex.I * z)))
    (X : ℂ → ℂ) (hX : ContDiff ℝ ∞ X) (hXK : HasCompactSupport X)
    (hXV : ∀ z ∈ ball (0 : ℂ) 2, X z = charField e z)
    (ψ : ℝ → ℂ → ℂ) (hψ : ContDiff ℝ ∞ (fun p : ℝ × ℂ => ψ p.1 p.2)) (hψ0 : ∀ y, ψ 0 y = y)
    (hψd : ∀ t y, HasDerivAt (fun s => ψ s y) (X (ψ t y)) t)
    (c : ℝ → ℂ) (hc : ContDiff ℝ 1 c) (hcA : ∀ t, c t ∈ closedBall (0 : ℂ) 1)
    (hw : HasLoopWind (fun t => c t - z₀) 1)
    (htr : ∀ t, liouville (e (c t)) (fderiv ℝ e (c t) (deriv c t)) ≠ 0) :
    InjOn (fun p : ℂ => ψ p.re (c p.im)) {p : ℂ | p.re < 0 ∧ p.im ∈ Ico (0 : ℝ) 1} := by
  sorry

end FiniteEnergyPlane
