-- Prove2me | Theorems.Thm_ALADIN_DualDecomp_argmax_display
-- name    : ALADIN.DualDecomp.argmax_display
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:46:09.527448+00:00
-- url     : https://prove2.me/theorems/f16d7e97-ee5b-4cd3-ae1c-480c94fdfc9a
-- title:
--   App. A, proof of Lemma 5 — λ − (M − I/μ)⁻¹g is the unique maximizer of ½(ν−λ)ᵀM(ν−λ) + νᵀg − ‖ν−λ‖²/(2μ)
-- statement:
--   Let $M\in\mathbb R^{m\times m}$ be symmetric negative semidefinite, $\mu > 0$, and $\lambda, g\in\mathbb R^m$. Define
--   $$\varphi(\nu) = \tfrac12(\nu-\lambda)^\top M(\nu-\lambda) + \nu^\top g - \frac{1}{2\mu}\|\nu-\lambda\|_2^2 .$$
--   Then $M - \frac1\mu I$ is invertible and
--   $$\nu^\star = \lambda - \Big(M - \frac1\mu I\Big)^{-1} g$$
--   is the unique maximizer of $\varphi$ over $\mathbb R^m$.
--
--   In the proof of Lemma 5, with $g = \nabla V(\lambda)$ and $M$ from (A.6), $\varphi$ is the dual objective of the QP (3.3) after the slack and $\Delta y$ have been eliminated, and the display identifies its maximizer $\lambda_{\mathrm{QP}}$ with the Levenberg–Marquardt dual Newton direction.
-- source:
--   Houska, Frasch, Diehl, An augmented Lagrangian based algorithm for distributed nonconvex optimization, SIAM J. Optim. 26 (2016), p. 1124, App. A, proof of Lemma 5, argmax display

import Mathlib

namespace ALADIN.DualDecomp

open Matrix

/-- App. A, proof of Lemma 5, p. 1124 (the argmax display): let `M ∈ ℝ^{m×m}` be symmetric and negative
semidefinite, `μ > 0`, `λ ∈ ℝᵐ` and `g ∈ ℝᵐ` (in the paper `g = ∇V(λ)`). Then `M − (1/μ) I` is invertible
and `ν⋆ = λ − (M − (1/μ) I)⁻¹ g` is the unique maximizer over `ℝᵐ` of
`ν ↦ ½ (ν − λ)ᵀ M (ν − λ) + νᵀ g − (1/(2μ)) ‖ν − λ‖²₂`. -/
theorem argmax_display {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ) (hM : (-M).PosSemidef)
    (μ : ℝ) (hμ : 0 < μ) (lam g : Fin m → ℝ) :
    let φ : (Fin m → ℝ) → ℝ := fun ν =>
      1 / 2 * ((ν - lam) ⬝ᵥ (M *ᵥ (ν - lam))) + ν ⬝ᵥ g - 1 / (2 * μ) * ((ν - lam) ⬝ᵥ (ν - lam))
    let νstar := lam - (M - μ⁻¹ • (1 : Matrix (Fin m) (Fin m) ℝ))⁻¹ *ᵥ g
    IsUnit (M - μ⁻¹ • (1 : Matrix (Fin m) (Fin m) ℝ)).det ∧
    IsMaxOn φ Set.univ νstar ∧
    ∀ ν, φ ν = φ νstar → ν = νstar := by sorry

end ALADIN.DualDecomp
