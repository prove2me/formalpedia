-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_AdicPoint_toOmega_act
-- name    : CerednikDrinfeld.FormalOmega.AdicPoint.toOmega_act
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/e7460546-537e-5fdb-bc9d-9400d79abb21
-- title:
--   GL₂(K)-equivariance of the adic coordinate map
-- statement:
--   Let $\mathcal{O}$ be a discrete valuation domain with fraction field $K$, let $\pi \in \mathcal{O}$, and let $C$ be a field equipped with a valuation with values in a linearly ordered commutative group with zero $\Gamma_0$ and with a $K$-algebra structure; let $R$ be a commutative $\mathcal{O}$-algebra mapping to $C$, all structure maps being compatible as $\mathcal{O}$-algebras. Let $\varpi$ be a pseudo-uniformizer, that is, an element $\varpi.\varpi \in K$ whose valuation in $C$ lies strictly between $0$ and $1$ and is cofinal in the sense that every nonzero $a \in K$ satisfies $v(\varpi)^N \le v(a) \le v(\varpi)^{-N}$ for some $N \in \mathbb{N}$. Assume `IsAdicFrame` $\pi\,\varpi\,R$: $\pi$ is irreducible, $R \to C$ is injective with image exactly the unit ball $\{v \le 1\}$, $R$ is complete for the $\pi$-adic filtration, the elements of $K$ of valuation $\le 1$ are exactly those coming from $\mathcal{O}$, the image of $K$ in $C$ is closed, and $\pi$ and $\varpi.\varpi$ have the same image in $C$. Let $g \in \mathrm{GL}_2(K)$ and let $x$ be an adic point, i.e. a system of Deligne data $x.\mathrm{pt}\,n$ over $R/\pi^n$ — for each full $\mathcal{O}$-lattice $M \subset K^2$ a submodule of the base change of $M$ with invertible quotient, monotone in $M$, equivariant for homotheties and nondegenerate at every prime — compatible under the transition maps $R/\pi^{n+1} \to R/\pi^n$. Then the coordinate $\mathrm{toOmega}$ of the translated point $x.\mathrm{act}\,g$, whose $n$-th datum is the pullback of $x.\mathrm{pt}\,n$ along $g^{-1}$, equals `Omega.pmoebius` applied to the image of $g$ in $\mathrm{PGL}_2(K)$ and to $\mathrm{toOmega}$ of $x$; here $\mathrm{toOmega}$ of an adic point is the unique $z \in C$ with $(z,1)$ on the associated line over $C$ when such a $z$ exists uniquely and $0$ otherwise, and `pmoebius` is the Möbius action on $\mathbb{P}^1(C)$ followed by the map sending $\infty$ to $0$ and a finite point to itself.
--
--   This is the equivariance of the coordinate that identifies adic points of the formal Deligne functor with points of the Drinfeld upper half-plane, in the form used in the Čerednik–Drinfeld uniformisation. It is used in the identification of the edge charts, in the surjectivity of the coordinate map onto the upper half-plane, and in the passage to quotients by discrete groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_AdicPoint_toOmega_act.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFrame

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega

theorem CerednikDrinfeld.FormalOmega.AdicPoint.toOmega_act
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] {π : 𝒪}
    {C : Type} [Field C] [Algebra K C] [DecidableEq C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
    {R : Type} [CommRing R] [Algebra 𝒪 R] [Algebra R C] [Algebra 𝒪 C] [IsScalarTower 𝒪 R C] [IsScalarTower 𝒪 K C]
    (ϖ : PseudoUniformizer K C) (hF : IsAdicFrame π ϖ R) (g : GL (Fin 2) K) (x : AdicPoint K π R) :
    (x.act g).toOmega C = Omega.pmoebius K (Matrix.ProjGenLinGroup.mk g) (x.toOmega C) := by sorry
