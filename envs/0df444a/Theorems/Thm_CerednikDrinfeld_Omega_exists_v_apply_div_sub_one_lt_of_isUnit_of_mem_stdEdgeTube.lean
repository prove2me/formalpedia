-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_v_apply_div_sub_one_lt_of_isUnit_of_mem_stdEdgeTube
-- name    : CerednikDrinfeld.Omega.exists_v_apply_div_sub_one_lt_of_isUnit_of_mem_stdEdgeTube
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/43b10903-9c6c-5890-a7ef-20ede3eccb03
-- title:
--   Units are monomials modulo principal units on the edge tube
-- statement:
--   Let $K_0$ be a field and $K$ a complete, algebraically closed field which is a $K_0$-algebra, carrying a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$. Let $\varpi$ be a pseudo-uniformiser, i.e. an element $\varpi \in K_0$ with $0 < v(\varpi) < 1$ in $K$ and such that every nonzero $a \in K_0$ satisfies $v(\varpi)^N \le v(a) \le v(\varpi)^{-N}$ for some $N \in \mathbb{N}$. Two further hypotheses on the value group are assumed: for all $x, y \in K$ with $v(x) < 1$ and $y \neq 0$ there is $n \in \mathbb{N}$ with $v(x)^n \le v(y)$; and for every $a \in K_0$ either $v(a) \le v(\varpi)$ or $1 \le v(a)$, so that no value of $K_0$ lies strictly between $v(\varpi)$ and $1$. Let $f$ be an element of `holRing` $\varpi$, the ring of functions on the Drinfel'd upper half-plane $\Omega = K \setminus K_0$ whose restriction to each affinoid `affinoid` $\varpi\, n$ is a uniform limit of a uniformly bounded sequence of rational functions without poles there, and assume $f$ is a unit of this ring. The assertion is that there exist $c \in K$ with $c \neq 0$ and $m \in \mathbb{Z}$ such that for every $z$ in the standard edge tube, that is every $z \in K$ outside the image of $K_0$ with $v(\varpi) < v(z) < 1$, one has $v\bigl(f(z)/(c z^m) - 1\bigr) < 1$ and $v(f(z)) = v(c)\, v(z)^m$.
--
--   On the annulus attached to an edge of the Bruhat–Tits tree, an invertible rigid-analytic function is a monomial $c z^m$ up to a factor that is a principal unit at every point; the second clause records the resulting equality of valuations, refining the purely valuation-theoretic form of this statement to a congruence modulo the principal units $\{u : v(u-1) < 1\}$. It is used in the construction of theta functions for the Cerednik–Drinfel'd uniformisation, where it enters the normalisation of $v(\theta)$ along the tubes of $\Omega$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_v_apply_div_sub_one_lt_of_isUnit_of_mem_stdEdgeTube.lean

import Definitions.Def_CerednikDrinfeld_OmegaTubes
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.exists_v_apply_div_sub_one_lt_of_isUnit_of_mem_stdEdgeTube
    {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hunif : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ∨ 1 ≤ Valued.v (algebraMap K₀ K a))
    (f : ↥(holRing ϖ)) (hf : IsUnit f) :
    ∃ (c : K) (m : ℤ), c ≠ 0 ∧
      ∀ (z : K) (hz : z ∈ stdEdgeTube ϖ),
        Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) ⟨z, hz.1⟩ / (c * z ^ m) - 1) < 1 ∧
        Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) ⟨z, hz.1⟩) = Valued.v c * Valued.v z ^ m := by sorry
