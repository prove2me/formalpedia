-- Prove2me | Theorems.Thm_AlgebraicGeometry_ProjSpace_isQuasicoherent_twist
-- name    : AlgebraicGeometry.ProjSpace.isQuasicoherent_twist
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/be453107-0ca6-59a8-9ada-7993a502529c
-- title:
--   Quasi-coherence of the twist datum on X → P^N_A
-- statement:
--   Let $A$ be a commutative ring, $N$ a natural number and $X$ a scheme; let $\pi : X \to \operatorname{Spec} A$ be a separated morphism and let $\varphi : X \to \operatorname{Proj}$ of the graded ring $\bigoplus_d \mathrm{MvPolynomial.homogeneousSubmodule}\,(\mathrm{Fin}\,(N+1))\,A$, i.e. of $A[x_0,\dots,x_N]$ with its standard grading, be an affine morphism; let $m$ be a natural number. The presheaf of modules `ProjSpace.twist π φ m` over $\pi$ assigns to an open $U \subseteq X$ the $A$-module and $\Gamma(X,U)$-module `twistObj π φ m U` of families $(g_i)_{i \in \mathrm{Fin}(N+1)}$ with $g_i \in \Gamma(X, U \sqcap \mathrm{pullbackChart}\,\varphi\,i)$ satisfying the compatibility predicate `TwistCompat φ m U`, restriction being componentwise restriction of sections. The assertion is that this presheaf satisfies `IsQuasicoherent`: for every affine open $U \subseteq X$ and every $f \in \Gamma(X,U)$, first, every section $x$ over the basic open $X_f \subseteq U$ admits an $n \in \mathbb{N}$ and a section $y$ over $U$ whose restriction to $X_f$ equals $f^n \cdot x$ (with $f^n$ restricted to $X_f$), and second, every section $y$ over $U$ restricting to $0$ on $X_f$ is annihilated by $f^n$ for some $n \in \mathbb{N}$.
--
--   This is the elementwise form of the statement that the pull-back $\varphi^*\mathcal{O}(m)$, written in the frames given by the standard coordinate charts of $\mathbb{P}^N_A$, is a quasi-coherent sheaf, i.e. that its sections over a basic open $X_f$ of an affine open $U$ form the localisation at $f$ of its sections over $U$. It is used in the cohomological study of these twists, for instance in the finiteness and flatness statements for their Čech cochains and in the construction of coherent quotients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_ProjSpace_isQuasicoherent_twist.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.ProjSpace.isQuasicoherent_twist
    {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
    (π : X ⟶ Spec (.of A)) [IsSeparated π]
    (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) [IsAffineHom φ] (m : ℕ) :
    (ProjSpace.twist π φ m).IsQuasicoherent := by sorry
