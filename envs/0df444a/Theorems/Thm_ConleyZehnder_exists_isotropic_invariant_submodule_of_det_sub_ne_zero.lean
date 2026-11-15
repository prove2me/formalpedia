-- Prove2me | Theorems.Thm_ConleyZehnder_exists_isotropic_invariant_submodule_of_det_sub_ne_zero
-- name    : ConleyZehnder.exists_isotropic_invariant_submodule_of_det_sub_ne_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-14T20:29:03.240215+00:00
-- url     : https://prove2.me/theorems/e9d552db-5a5e-48eb-b05e-b74875362354
-- title:
--   A symplectic matrix without unit-circle eigenvalues has an invariant isotropic complex subspace of half dimension
-- statement:
--   Let $A\in\mathrm{Sp}(2n,\mathbb R)$ have no eigenvalue of modulus $1$: $\det(A-z I)\ne0$ for all $z\in\mathbb C$ with $|z|=1$. Then there is a complex linear subspace $L\subseteq\mathbb C^{2n}$ with
--
--   - $\dim_{\mathbb C}L\ge n$,
--   - $AL\subseteq L$ (for the complexification of $A$),
--   - $\bar L=L$ (closed under complex conjugation),
--   - $L$ isotropic for the complex bilinear form $\omega(v,w)=v^{\mathsf T}J_0w$.
--
--   This is a structural fact about hyperbolic symplectic matrices, used for signature and Conley–Zehnder computations of hyperbolic orbits.
--
--   Formalization Note: `Mat n` is `Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ`, `IsSymplectic` and `J₀ n` are the platform definitions; the complexification is `A.map (fun x : ℝ => (x : ℂ))`, conjugation is `star`, and $\omega$ is written as `v ⬝ᵥ (J₀ᶜ *ᵥ w)`.
-- source:
--   Standard (linear symplectic algebra)

import Definitions.Def_ConleyZehnder_Setting

namespace ConleyZehnder

open Matrix Module

/-- Let `A ∈ Sp(2n, ℝ)` have no eigenvalue on the unit circle. Then there is a complex subspace
`L ⊆ ℂ^{2n}` of dimension at least `n` that is invariant under (the complexification of) `A`,
closed under complex conjugation, and isotropic for the bilinear form
`ω(v, w) = vᵀ J₀ w`. -/
theorem exists_isotropic_invariant_submodule_of_det_sub_ne_zero {n : ℕ} {A : Mat n}
    (hs : IsSymplectic A)
    (hcirc : ∀ z : ℂ, ‖z‖ = 1 → (A.map (fun x : ℝ => (x : ℂ)) - z • 1).det ≠ 0) :
    ∃ L : Submodule ℂ (Fin n ⊕ Fin n → ℂ), n ≤ finrank ℂ L ∧
      (∀ v ∈ L, A.map (fun x : ℝ => (x : ℂ)) *ᵥ v ∈ L) ∧ (∀ v ∈ L, star v ∈ L) ∧
      ∀ v ∈ L, ∀ w ∈ L, v ⬝ᵥ ((J₀ n).map (fun x : ℝ => (x : ℂ)) *ᵥ w) = 0 := by
  sorry

end ConleyZehnder
