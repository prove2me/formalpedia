-- Prove2me | Theorems.Thm_FamousTheorems_jacobi_sum_gauss_sums_7b
-- name    : FamousTheorems.jacobi_sum_gauss_sums_7b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:34:37.963469+00:00
-- url     : https://prove2.me/theorems/da470482-cf9b-4ed8-9b9c-f794de6e5a82
-- title:
--   Jacobi sums in terms of Gauss sums
-- statement:
--   **Jacobi sums in terms of Gauss sums.** Let $F$ be a finite field, $F'$ a field in which $|F|\neq0$, $\chi,\varphi$ multiplicative characters of $F$ with values in $F'$ such that $\chi\varphi$ is nontrivial, and $\psi$ a primitive additive character of $F$ with values in $F'$. Then
--   $$J(\chi,\varphi)=\frac{g(\chi,\psi)\,g(\varphi,\psi)}{g(\chi\varphi,\psi)},$$
--   where $J(\chi,\varphi)=\sum_{x}\chi(x)\varphi(1-x)$ is the Jacobi sum and $g(\chi,\psi)=\sum_x\chi(x)\psi(x)$ the Gauss sum.
--
--   This identity is the finite field analogue of the formula $B(a,b)=\Gamma(a)\Gamma(b)/\Gamma(a+b)$ for the beta function. It is used to count points on diagonal equations such as Fermat curves, as in Weil's 1949 paper that led to the Weil conjectures, and to prove $p=a^2+b^2$ for primes $p\equiv1\pmod4$ and related representations.
--
--   **Formalization note.** Mathlib's `jacobiSum_eq_gaussSum_mul_gaussSum_div_gaussSum`. `MulChar F F'` is the type of multiplicative characters, extended by $0$ at $0$, and `AddChar.IsPrimitive` says that the characters $x\mapsto\psi(ax)$ for $a\neq0$ are nontrivial.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `jacobiSum_eq_gaussSum_mul_gaussSum_div_gaussSum`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem jacobi_sum_gauss_sums_7b {F F' : Type*} [Fintype F] [Field F] [Field F'] (hF : (Fintype.card F : F') ≠ 0)
    {χ φ : MulChar F F'} (hχφ : χ * φ ≠ 1) {ψ : AddChar F F'} (hψ : ψ.IsPrimitive) :
    jacobiSum χ φ = gaussSum χ ψ * gaussSum φ ψ / gaussSum (χ * φ) ψ := by sorry

end FamousTheorems
