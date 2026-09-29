-- Prove2me | Theorems.Thm_AlgebraicCurve_linearIndependent_pow_mul_of_flagAdaptedBasisAt_of_ell_eq
-- name    : AlgebraicCurve.linearIndependent_pow_mul_of_flagAdaptedBasisAt_of_ell_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/b2fb7a19-8d2c-5cfd-95a1-d44e0315ee19
-- title:
--   Global independence of a pole-filtration-adapted family x^j y_σ
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, let $x \in F$, and let $D$ be a divisor of $F/K$, i.e. a finitely supported function on the places of $F$ over $K$ with integer values, subject to $D(v) = \max(0, -\operatorname{ord}_v x)$ at every place $v$, so that $D$ is the pole divisor of $x$. Assume every Riemann–Roch space $\mathcal L(M \cdot D) = \{f \in F : v(f) \le \exp(M \cdot D(v)) \text{ for all } v\}$, $M \in \mathbb N$, is finite-dimensional over $K$, and fix naturals $M_0, d, g_0$ such that $\dim_K \mathcal L(N \cdot D) = N d + 1 - g_0$ as an integer identity for every $N \ge M_0$. Let $d' \in \mathbb N$ and let $y : \mathrm{Fin}\, d' \to F$, $e : \mathrm{Fin}\, d' \to \mathbb N$ satisfy $e(\sigma) \le M_0 + 1$ and $y_\sigma \in \mathcal L(e(\sigma) \cdot D)$ for each $\sigma$. Assume further that for every $M$ the space $\mathcal L(M \cdot D)$ is contained in the $K$-span of $\{x^j y_\sigma : j + e(\sigma) \le M\}$, and that for every $M \le M_0 + 1$ the family $(\sigma, j) \mapsto x^j y_\sigma$ indexed by the pairs with $j + e(\sigma) \le M$ is $K$-linearly independent. Then the whole family $(\sigma, j) \mapsto x^j y_\sigma$, indexed by all of $\mathrm{Fin}\, d' \times \mathbb N$, is $K$-linearly independent.
--
--   This is the step upgrading level-by-level independence, valid up to the level $M_0 + 1$ where the Riemann–Roch dimension count becomes exact, to independence of the full infinite family $\{x^j y_\sigma\}$; it is the classical reduced-basis argument for the pole filtration of a function field by the powers of a fixed element, going back to Deuring and Roquette. It feeds into [`AlgebraicCurve.exists_flagAdaptedBasis_lSpace_nsmul_poleDivisor`](thm.html#AlgebraicCurve.exists_flagAdaptedBasis_lSpace_nsmul_poleDivisor), which produces a basis of $F$ adapted to the filtration by the spaces $\mathcal L(M \cdot D)$, and it uses the compatibility of multiplication by $x$ with this filtration recorded in [`AlgebraicCurve.mul_mem_lSpace_nsmul_succ_and_reflects_of_poleDivisor`](thm.html#AlgebraicCurve.mul_mem_lSpace_nsmul_succ_and_reflects_of_poleDivisor).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_linearIndependent_pow_mul_of_flagAdaptedBasisAt_of_ell_eq.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.linearIndependent_pow_mul_of_flagAdaptedBasisAt_of_ell_eq
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (x : F) (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x))
    (hFD : ∀ M : ℕ, FiniteDimensional K ↥(LSpace (M • D)))
    (M₀ d g₀ : ℕ)
    (hell : ∀ N, M₀ ≤ N → (ell (N • D) : ℤ) = N * d + 1 - g₀)
    {d' : ℕ} (y : Fin d' → F) (e : Fin d' → ℕ)
    (hle : ∀ σ, e σ ≤ M₀ + 1) (hy : ∀ σ, y σ ∈ LSpace ((e σ) • D))
    (hspan : ∀ M : ℕ, (LSpace (M • D) : Submodule K F)
      ≤ Submodule.span K {z | ∃ σ j, j + e σ ≤ M ∧ z = x ^ j * y σ})
    (hLIat : ∀ M ≤ M₀ + 1, LinearIndependent K
      (fun p : {p : Fin d' × ℕ // p.2 + e p.1 ≤ M} => x ^ p.val.2 * y p.val.1)) :
    LinearIndependent K (fun p : Fin d' × ℕ => x ^ p.2 * y p.1) := by sorry
