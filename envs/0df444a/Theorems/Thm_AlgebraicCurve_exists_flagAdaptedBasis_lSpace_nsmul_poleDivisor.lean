-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_flagAdaptedBasis_lSpace_nsmul_poleDivisor
-- name    : AlgebraicCurve.exists_flagAdaptedBasis_lSpace_nsmul_poleDivisor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/7141b144-e97d-5b50-811e-ba7aa15d9e34
-- title:
--   Flag-adapted basis for the pole filtration of x
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $x \in F$ be transcendental over $K$. Let $D$ be a divisor of $F/K$, i.e. a finitely supported function from the places of $F/K$ (valuation subrings of $F$ containing the image of $K$, proper and with principal ideals) to $\mathbb{Z}$, and assume $D$ is the pole divisor of $x$, in the sense that $D(v) = \max(0, -\operatorname{ord}_v x)$ at every place $v$. Assume that for every $M \in \mathbb{N}$ the Riemann–Roch space $\mathcal{L}(M \cdot D) = \{f \in F : v(f) \le \exp(M \cdot D(v)) \text{ for all } v\}$ is finite-dimensional over $K$, that $\ell(0) = \dim_K \mathcal{L}(0) = 1$, and that for naturals $M_0, d, g_0$ with $1 \le d$ one has $\ell(N \cdot D) = Nd + 1 - g_0$ as integers for all $N \ge M_0$. Then there exist $d' \in \mathbb{N}$, elements $y_\sigma \in F$ and naturals $e_\sigma$ for $\sigma \in \mathrm{Fin}\,d'$ such that: for every $M \in \mathbb{N}$, $\mathcal{L}(M \cdot D)$ is contained in the $K$-span of $\{x^j y_\sigma : j + e_\sigma \le M\}$; the whole family $(x^j y_\sigma)_{(\sigma,j) \in \mathrm{Fin}\,d' \times \mathbb{N}}$ is $K$-linearly independent; and $y_\sigma \in \mathcal{L}(e_\sigma \cdot D)$ for each $\sigma$.
--
--   This is the existence of a basis adapted to the pole filtration $\mathcal{L}(0) \subseteq \mathcal{L}(D) \subseteq \mathcal{L}(2D) \subseteq \cdots$ of the function field $F/K$ attached to a transcendental element $x$, in the reduced form used by Deuring and Roquette: every $\mathcal{L}(M \cdot D)$ is spanned by the monomials $x^j y_\sigma$ of weight $j + e_\sigma \le M$, and these monomials are globally independent. It feeds the analysis of regular prolongations, being used in [`AlgebraicCurve.RegularProlongation.exists_finset_forall_valuation_eq_one_forall_exists_forall_ell_nsmul_le`](thm.html#AlgebraicCurve.RegularProlongation.exists_finset_forall_valuation_eq_one_forall_exists_forall_ell_nsmul_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_flagAdaptedBasis_lSpace_nsmul_poleDivisor.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.exists_flagAdaptedBasis_lSpace_nsmul_poleDivisor
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x))
    (hFD : ∀ M : ℕ, FiniteDimensional K ↥(LSpace (M • D)))
    (hell0 : ell (0 : Divisor K F) = 1)
    (M₀ d g₀ : ℕ) (hd : 1 ≤ d)
    (hell : ∀ N, M₀ ≤ N → (ell (N • D) : ℤ) = N * d + 1 - g₀) :
    ∃ (d' : ℕ) (y : Fin d' → F) (e : Fin d' → ℕ),
      (∀ M : ℕ, (LSpace (M • D) : Submodule K F)
        ≤ Submodule.span K {z | ∃ σ j, j + e σ ≤ M ∧ z = x ^ j * y σ}) ∧
      LinearIndependent K (fun p : Fin d' × ℕ => x ^ p.2 * y p.1) ∧
      (∀ σ, y σ ∈ LSpace ((e σ) • D)) := by sorry
