-- Prove2me | Theorems.Thm_FiniteEnergyPlane_eq_one_of_im_conj_mul_apply_le_zero
-- name    : FiniteEnergyPlane.eq_one_of_im_conj_mul_apply_le_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-01T22:25:40.487098+00:00
-- url     : https://prove2.me/theorems/1bfb147f-d9d1-405a-bdd4-11017cbb9562
-- title:
--   A positive eigenvalue of an area-preserving linear map of the plane is 1 when the twist form has constant sign near the eigenvector
-- statement:
--   Let $L:\mathbb{C}\to\mathbb{C}$ be $\mathbb{R}$-linear and preserve the area form $\omega(z,w)=\operatorname{Im}(\bar z w)$, i.e. $\omega(Lz,Lw)=\omega(z,w)$ for all $z,w$. Let $\alpha\in\mathbb{R}$, $u=e^{i\alpha}$, and suppose $Lu=cu$ with $c>0$. Suppose moreover that the function $\beta\mapsto\omega(e^{i\beta},Le^{i\beta})$ is $\le0$ on a neighbourhood of $\alpha$, or is $\ge0$ on a neighbourhood of $\alpha$. Then $c=1$.
--
--   A linear-algebra fact about $\mathrm{Sp}(2)=\mathrm{SL}(2,\mathbb{R})$: a direction that is extremal for the rotation of directions under $L$ and is mapped to a positive multiple of itself is fixed by $L$. It identifies fixed vectors of monodromy matrices, i.e. periodic solutions of linear Hamiltonian ODEs in the plane.
--
--   **Formalization Note** $L$ is `L : ℂ →ₗ[ℝ] ℂ`, $\omega(z,w)$ is `(conj z * w).im`; the neighbourhood conditions are `∀ᶠ β : ℝ in 𝓝 α, …` and the conclusion is `c = 1`.
-- source:
--   Elementary linear algebra of Sp(2) = SL(2,R); used in C. Wendl, Lectures on Symplectic Field Theory (2026 notes), arXiv:1612.01009, Section 3.7, proof of Theorem 3.7.1.

import Mathlib

namespace FiniteEnergyPlane

open Filter Topology ComplexConjugate

/-- Let `L : ℂ → ℂ` be `ℝ`-linear and preserve `ω(z, w) = Im (z̄ w)`. If `u = e^{iα}` satisfies
`L u = c u` with `c > 0`, and `β ↦ ω(e^{iβ}, L e^{iβ})` has constant sign (`≤ 0` throughout, or
`≥ 0` throughout) on a neighbourhood of `α`, then `c = 1`. -/
theorem eq_one_of_im_conj_mul_apply_le_zero {L : ℂ →ₗ[ℝ] ℂ}
    (hL : ∀ z w, (conj (L z) * L w).im = (conj z * w).im) {α c : ℝ} (hc : 0 < c)
    (hu : L (Complex.exp (α * Complex.I)) = c * Complex.exp (α * Complex.I))
    (hsign : (∀ᶠ β : ℝ in 𝓝 α, (conj (Complex.exp ((β : ℂ) * Complex.I)) *
        L (Complex.exp ((β : ℂ) * Complex.I))).im ≤ 0) ∨
      (∀ᶠ β : ℝ in 𝓝 α, 0 ≤ (conj (Complex.exp ((β : ℂ) * Complex.I)) *
        L (Complex.exp ((β : ℂ) * Complex.I))).im)) : c = 1 := by
  sorry

end FiniteEnergyPlane
