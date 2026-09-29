-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_smul_stdVertex_eq_of_mem_affinoid_zero
-- name    : CerednikDrinfeld.Omega.smul_stdVertex_eq_of_mem_affinoid_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/f20c265a-f86b-5b8c-89b9-50605ba74af2
-- title:
--   Points of the level-zero affinoid determine their vertex
-- statement:
--   Let $R$ be a discrete valuation ring (a commutative domain with the discrete valuation ring structure) with fraction field $K_0$, let $\varpi \in R$ be irreducible, and let $K$ be a field extension of $K_0$ equipped with a valuation taking values in a linearly ordered commutative group with zero $\Gamma_0$ (together with decidable equality on $K$). Two compatibility hypotheses are imposed: every element of $R$ has valuation at most $1$ in $K$, and conversely every $a \in K_0$ whose image in $K$ has valuation at most $1$ lies in the image of $R$. Let $\varpi_1$ be a pseudo-uniformiser of $K_0$ relative to $K$, i.e. an element of $K_0$ whose valuation in $K$ lies strictly between $0$ and $1$ and such that the valuation of every nonzero element of $K_0$ is squeezed between $v(\varpi_1)^{N}$ and $v(\varpi_1)^{-N}$ for some $N$. Let $x \in K$ and let $g, g' \in \mathrm{GL}_2(K_0)$. Assume that both $h^{-1}\cdot x$ for $h$ the class of $g$ and for $h$ the class of $g'$ in $\mathrm{PGL}_2(K_0)$ — the fractional-linear action on $\mathbb{P}^1(K) = K \cup \{\infty\}$, with $\infty$ sent to $0$ when forming the affine coordinate — lie in the level-zero affinoid $\{z \in K : v(z) \le 1 \text{ and } v(z - a) \ge 1 \text{ for all } a \in K_0 \text{ with } v(a) \le 1\}$. Then $g$ and $g'$ send the standard vertex of the lattice tree over $(R, K_0)$ — the homothety class of the lattice of vectors in $K_0^2$ with both coordinates in $R$ — to the same vertex: $g \cdot v_0 = g' \cdot v_0$.
--
--   This is the disjointness of the fibres of the reduction map from Drinfeld's $p$-adic upper half plane to the Bruhat–Tits tree of $\mathrm{PGL}_2(K_0)$: a point of $\mathbb{P}^1(K)$ lying in the level-zero affinoid translated by $g$ and by $g'$ forces $g$ and $g'$ to determine the same vertex, so the vertex attached to such a point is well defined. It is used for the rigidity statement [`CerednikDrinfeld.Omega.eq_one_of_pmoebius_eq_of_mem_affinoid_zero`](thm.html#CerednikDrinfeld.Omega.eq_one_of_pmoebius_eq_of_mem_affinoid_zero) and, further downstream, in the construction of period data for Mumford quotients and theta-function factorisations of periods on $\mathrm{Pic}^0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_smul_stdVertex_eq_of_mem_affinoid_zero.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.smul_stdVertex_eq_of_mem_affinoid_zero
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ : R) (hϖ : Irreducible ϖ)
    (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a)
    (ϖ₁ : PseudoUniformizer K₀ K)
    {x : K} (g g' : GL (Fin 2) K₀)
    (hx  : pmoebius K₀ (Matrix.ProjGenLinGroup.mk g)⁻¹ x ∈ affinoid ϖ₁ 0)
    (hx' : pmoebius K₀ (Matrix.ProjGenLinGroup.mk g')⁻¹ x ∈ affinoid ϖ₁ 0) :
    g • LT.LatticeTree.stdVertex R K₀ = g' • LT.LatticeTree.stdVertex R K₀ := by sorry
