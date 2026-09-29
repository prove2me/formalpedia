-- Prove2me | Theorems.Thm_CuspForm_exists_mul_E4_pow_mul_E6_pow_eq_iff
-- name    : CuspForm.exists_mul_E4_pow_mul_E6_pow_eq_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/0286c65e-0ac4-5406-9efb-6d4498dac1aa
-- title:
--   Recognising cusp forms through F = f E₄ᵃE₆ᵇ/Δ^m
-- statement:
--   Let $\Gamma$ be a finite-index subgroup of $\mathrm{SL}_2(\mathbb{Z})$, let $k$ be an integer and let $a,b,m$ be natural numbers with $k + 4a + 6b = 12m$. Let $F\colon\mathfrak{H}\to\mathbb{C}$ be holomorphic (differentiable for the complex model with corners on the upper half-plane). Then the existence of a cusp form $f$ of weight $k$ for the image of $\Gamma$ in $\mathrm{GL}_2(\mathbb{R})$, in Mathlib's sense, satisfying $f(\tau)\,\bigl(E_4(\tau)^a E_6(\tau)^b\bigr) = F(\tau)\,\Delta(\tau)^m$ for every $\tau\in\mathfrak{H}$, where $E_4,E_6$ are the level-one normalised Eisenstein series and $\Delta$ is the discriminant form, is equivalent to the conjunction of the following four conditions: (i) there is a holomorphic $G$ on $\mathfrak{H}$ with $(F\Delta^m)^3 = E_4^{3a}\,G$ pointwise; (ii) there is a holomorphic $G$ on $\mathfrak{H}$ with $(F\Delta^m)^2 = E_6^{2b}\,G$ pointwise; (iii) for every $A \in \mathrm{SL}_2(\mathbb{Z})$ the function $\tau \mapsto F(A\cdot\tau)\,\Delta(\tau)^m$ vanishes at $i\infty$; and (iv) $F(\gamma\cdot\tau) = F(\tau)$ for all $\gamma\in\Gamma$ and all $\tau\in\mathfrak{H}$.
--
--   This is the recognition principle for the level-one weight lowering $f \mapsto F = f\,E_4^aE_6^b/\Delta^m$, identifying cusp forms of weight $k$ on $\Gamma$ with holomorphic $\Gamma$-invariant functions on $\mathfrak{H}$ cut out by the two polynomial divisibility conditions (which encode holomorphy at the elliptic points) together with vanishing at the cusps. It is used in the treatment of rationality of spaces of cusp forms, where such conditions are transported under field automorphisms: it is cited by [`CuspForm.exists_gamma1_frickeRational_sigmaTransport`](thm.html#CuspForm.exists_gamma1_frickeRational_sigmaTransport), [`CuspForm.exists_gamma1_qCoeff_eq_algEquiv_apply_of_even`](thm.html#CuspForm.exists_gamma1_qCoeff_eq_algEquiv_apply_of_even) and [`CuspForm.span_frickeRational_E4_pow_E6_pow_eq_top`](thm.html#CuspForm.span_frickeRational_E4_pow_E6_pow_eq_top).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_mul_E4_pow_mul_E6_pow_eq_iff.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Manifold MatrixGroups ModularForm

theorem CuspForm.exists_mul_E4_pow_mul_E6_pow_eq_iff (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (k : ℤ) (a b m : ℕ) (hk : k + 4 * a + 6 * b = 12 * m)
    (F : UpperHalfPlane → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) :
    (∃ f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k, ∀ τ : UpperHalfPlane,
        f τ * (ModularForm.E₄ τ ^ a * ModularForm.E₆ τ ^ b) =
          F τ * ModularForm.discriminant τ ^ m) ↔
      ((∃ G : UpperHalfPlane → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G ∧ ∀ τ : UpperHalfPlane,
          (F τ * ModularForm.discriminant τ ^ m) ^ 3 = ModularForm.E₄ τ ^ (3 * a) * G τ) ∧
        (∃ G : UpperHalfPlane → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G ∧ ∀ τ : UpperHalfPlane,
          (F τ * ModularForm.discriminant τ ^ m) ^ 2 = ModularForm.E₆ τ ^ (2 * b) * G τ) ∧
        (∀ A : SL(2, ℤ), UpperHalfPlane.IsZeroAtImInfty
          ((F ∘ (A • ·)) * ModularForm.discriminant ^ m)) ∧
        ∀ γ ∈ Γ, ∀ τ : UpperHalfPlane, F (γ • τ) = F τ) := by sorry
