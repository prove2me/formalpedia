-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_flagAdaptedBasisAt_lSpace_nsmul_poleDivisor_succ
-- name    : AlgebraicCurve.exists_flagAdaptedBasisAt_lSpace_nsmul_poleDivisor_succ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/3f1d47c7-f8d3-5512-8bca-4f3ee5d2cbfe
-- title:
--   Inductive step for a reduced basis adapted to the pole filtration
-- statement:
--   Let $K \subseteq F$ be fields with $F$ a $K$-algebra, and let $x \in F$ be transcendental over $K$. Let $D$ be a divisor on $F/K$, i.e. a finitely supported function from the places of $F/K$ (valuation subrings of $F$ containing the image of $K$, proper in $F$, with principal ideal ring structure) to $\mathbb Z$, and assume $D$ is the pole divisor of $x$: $D(v) = \max(0, -\operatorname{ord}_v x)$ for every place $v$, where $\operatorname{ord}_v x = -\log v(x)$ for the adic valuation $v$ attached to the place. Assume each space $\mathcal L(M \cdot D) = \{f \in F : v(f) \le \exp(M\,D(v)) \text{ for all } v\}$ is finite-dimensional over $K$ for $M \in \mathbb N$, and that $\mathcal L(0)$ has $K$-dimension $1$. Let $M_1 \in \mathbb N$, let $d' \in \mathbb N$, and let $y : \mathrm{Fin}\,d' \to F$, $e : \mathrm{Fin}\,d' \to \mathbb N$ satisfy $e_\sigma \le M_1$ and $y_\sigma \in \mathcal L(e_\sigma \cdot D)$ for all $\sigma$, and, for every $M \le M_1$, both: $\mathcal L(M \cdot D)$ is contained in the $K$-span of $\{x^j y_\sigma : j + e_\sigma \le M\}$, and the family $(x^j y_\sigma)$ indexed by the pairs $(\sigma, j)$ with $j + e_\sigma \le M$ is $K$-linearly independent. Then there exist $d''$, $y' : \mathrm{Fin}\,d'' \to F$ and $e' : \mathrm{Fin}\,d'' \to \mathbb N$ with $e'_\sigma \le M_1 + 1$, $y'_\sigma \in \mathcal L(e'_\sigma \cdot D)$, and the same spanning and linear independence properties for all $M \le M_1 + 1$.
--
--   This is the inductive step in the Deuring–Roquette construction of a basis of $F$ over $K(x)$ adapted to the filtration by the pole divisor of $x$: the data $(y_\sigma, e_\sigma)$ simultaneously give bases of all $\mathcal L(M \cdot D)$ with $M \le M_1$ in the form $x^j y_\sigma$, and the statement extends such data from level $M_1$ to level $M_1 + 1$. It is used by [`AlgebraicCurve.exists_flagAdaptedBasisAt_lSpace_nsmul_poleDivisor`](thm.html#AlgebraicCurve.exists_flagAdaptedBasisAt_lSpace_nsmul_poleDivisor), which iterates it, and it invokes [`AlgebraicCurve.mul_mem_lSpace_nsmul_succ_and_reflects_of_poleDivisor`](thm.html#AlgebraicCurve.mul_mem_lSpace_nsmul_succ_and_reflects_of_poleDivisor) for the behaviour of multiplication by $x$ on the filtration.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_flagAdaptedBasisAt_lSpace_nsmul_poleDivisor_succ.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.exists_flagAdaptedBasisAt_lSpace_nsmul_poleDivisor_succ
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x))
    (hFD : ∀ M : ℕ, FiniteDimensional K ↥(LSpace (M • D)))
    (hell0 : ell (0 : Divisor K F) = 1) (M₁ : ℕ)
    {d' : ℕ} (y : Fin d' → F) (e : Fin d' → ℕ)
    (hle : ∀ σ, e σ ≤ M₁) (hy : ∀ σ, y σ ∈ LSpace ((e σ) • D))
    (hspan : ∀ M ≤ M₁, (LSpace (M • D) : Submodule K F)
      ≤ Submodule.span K {z | ∃ σ j, j + e σ ≤ M ∧ z = x ^ j * y σ})
    (hLI : ∀ M ≤ M₁, LinearIndependent K
      (fun p : {p : Fin d' × ℕ // p.2 + e p.1 ≤ M} => x ^ p.val.2 * y p.val.1)) :
    ∃ (d'' : ℕ) (y' : Fin d'' → F) (e' : Fin d'' → ℕ),
      (∀ σ, e' σ ≤ M₁ + 1) ∧
      (∀ σ, y' σ ∈ LSpace ((e' σ) • D)) ∧
      (∀ M ≤ M₁ + 1, (LSpace (M • D) : Submodule K F)
        ≤ Submodule.span K {z | ∃ σ j, j + e' σ ≤ M ∧ z = x ^ j * y' σ}) ∧
      (∀ M ≤ M₁ + 1, LinearIndependent K
        (fun p : {p : Fin d'' × ℕ // p.2 + e' p.1 ≤ M} => x ^ p.val.2 * y' p.val.1)) := by sorry
