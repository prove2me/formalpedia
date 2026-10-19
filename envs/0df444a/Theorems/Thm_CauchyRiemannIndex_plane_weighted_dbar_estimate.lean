-- Prove2me | Theorems.Thm_CauchyRiemannIndex_plane_weighted_dbar_estimate
-- name    : CauchyRiemannIndex.plane_weighted_dbar_estimate
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-17T11:50:46.811748+00:00
-- url     : https://prove2.me/theorems/4afcf7d0-2152-4b56-a03b-6c704e9a2de1
-- title:
--   Weighted L² estimate ∫|z|²|u|² ≤ ∫|∂̄u + z̄ū|² for compactly supported u on ℂ
-- statement:
--   Let $\bar\partial=\partial_s+i\partial_t$ on $\mathbb{C}$, $z=s+it$. For every compactly supported $C^1$ map $u:\mathbb{C}\to\mathbb{C}$,
--   $$\int_{\mathbb{C}}|z|^2\,|u(z)|^2\,dz\;\le\;\int_{\mathbb{C}}\big|\bar\partial u(z)+\bar z\,\overline{u(z)}\big|^2\,dz .$$
--
--   This weighted $L^2$ bound for the real-linear operator $u\mapsto\bar\partial u+\bar z\,\bar u$ controls compactly supported maps by their image.
--
--   **Formalization Note** $\partial_s u$, $\partial_t u$ are `fderiv ℝ u z 1` and `fderiv ℝ u z Complex.I`; $C^1$ is `ContDiff ℝ 1 u`; compact support is `HasCompactSupport u`; integrals are Bochner integrals for `volume` on `ℂ`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 5, Proposition 5.20, p. 96 (auxiliary lemma)

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

namespace CauchyRiemannIndex

open MeasureTheory

/-- Let `∂̄ = ∂ₛ + i ∂ₜ` on `ℂ`, `z = s + it`. For every compactly supported `C¹` map
`u : ℂ → ℂ`,
`∫ |z|² |u|² ≤ ∫ |∂̄u + z̄ ū|²`
over the plane (Lebesgue measure).

This is the weighted `L²` estimate for the real-linear operator `u ↦ ∂̄u + z̄ ū`; here
`∂ₛu = Du(z) 1` and `∂ₜu = Du(z) i`. -/
theorem plane_weighted_dbar_estimate (u : ℂ → ℂ) (hu : ContDiff ℝ 1 u)
    (hc : HasCompactSupport u) :
    ∫ z, ‖z‖ ^ 2 * ‖u z‖ ^ 2 ≤
      ∫ z, ‖fderiv ℝ u z 1 + Complex.I * fderiv ℝ u z Complex.I +
        (starRingEnd ℂ) z * (starRingEnd ℂ) (u z)‖ ^ 2 := by
  sorry

end CauchyRiemannIndex
