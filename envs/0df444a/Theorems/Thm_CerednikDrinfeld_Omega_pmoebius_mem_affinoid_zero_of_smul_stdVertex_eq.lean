-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_pmoebius_mem_affinoid_zero_of_smul_stdVertex_eq
-- name    : CerednikDrinfeld.Omega.pmoebius_mem_affinoid_zero_of_smul_stdVertex_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/14aa6352-5b3e-5e1c-a0d1-22de55a4a370
-- title:
--   Stabiliser of the standard vertex preserves the level-zero affinoid
-- statement:
--   Let $R$ be a discrete valuation domain with fraction field $K_0$, and let $K$ be a field extension of $K_0$ with decidable equality, carrying a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$. Assume the two compatibility hypotheses `hint`, that $v(a) \le 1$ for the image in $K$ of every $a \in R$, and `hv`, that every $a \in K_0$ whose image in $K$ satisfies $v(a) \le 1$ lies in the image of $R$. Let $\varpi_1$ be a pseudo-uniformiser, i.e. an element $\varpi \in K_0$ with $0 < v(\varpi) < 1$ in $K$ such that for each nonzero $a \in K_0$ there is $N \in \mathbb{N}$ with $v(\varpi)^N \le v(a) \le v(\varpi)^{-N}$. Let $h \in GL_2(K_0)$ fix the standard vertex, the homothety class of the lattice of those vectors in $K_0^2$ both of whose coordinates lie in $R$. Then the level-$0$ affinoid $\{z \in K \mid v(z) \le 1 \text{ and } v(z - a) \ge 1 \text{ for all } a \in K_0 \text{ with } v(a) \le 1\}$ is carried into itself by the Möbius action of the class of $h$ in $PGL_2(K_0)$ (with $\infty$ sent to $0$ by the chosen affine coordinate); that is, $w$ in this set implies that the image of $w$ lies in it as well.
--
--   This is the statement that the standard vertex fibre $\Omega_0$ of the Drinfeld upper half plane is stable under the stabiliser $K_0^\times \cdot GL_2(R)$ of the standard vertex of the Bruhat–Tits tree. It underlies the reduction arguments for theta functions and for the Mumford-curve description of $\Omega$ modulo a discrete group, and is used by the results on valuations of theta products and on neighbours of the standard vertex.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_pmoebius_mem_affinoid_zero_of_smul_stdVertex_eq.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Omega CerednikDrinfeld.Mumford MulAction

theorem CerednikDrinfeld.Omega.pmoebius_mem_affinoid_zero_of_smul_stdVertex_eq
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a)
    (ϖ₁ : PseudoUniformizer K₀ K)
    (h : GL (Fin 2) K₀) (hh : h • LT.LatticeTree.stdVertex R K₀ = LT.LatticeTree.stdVertex R K₀)
    {w : K} (hw : w ∈ affinoid ϖ₁ 0) :
    pmoebius K₀ (Matrix.ProjGenLinGroup.mk h) w ∈ affinoid ϖ₁ 0 := by sorry
