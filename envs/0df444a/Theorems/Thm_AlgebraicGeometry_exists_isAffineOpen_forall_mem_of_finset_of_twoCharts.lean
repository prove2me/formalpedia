-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_finset_of_twoCharts
-- name    : AlgebraicGeometry.exists_isAffineOpen_forall_mem_of_finset_of_twoCharts
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/0ce7f2ab-4edb-577e-bc08-8ee1e8a74a9b
-- title:
--   Finite sets in a two-chart scheme lie in affine opens
-- statement:
--   Let $R$ be a commutative ring, $X$ a scheme, and $c : X \to \operatorname{Spec} R$ a morphism of schemes. Let $U, V$ be open subschemes of $X$, both assumed affine open, with $U \sqcup V = \top$, i.e. $U \cup V = X$. Let $f \in \Gamma(X, U)$ and $g \in \Gamma(X, V)$ be sections of the structure sheaf over $U$ and over $V$ respectively, and assume that the open $U \cap V$ equals both the basic open $X_f$ of $f$ and the basic open $X_g$ of $g$; assume furthermore that the product of the restriction of $f$ along $U \cap V \le U$ with the restriction of $g$ along $U \cap V \le V$ is the unit section $1$ of $\Gamma(X, U \cap V)$. Then for every finite set $F$ of points of $X$ there exist an open $W \subseteq X$ which is an affine open and contains every $x \in F$.
--
--   This is the standard criterion that a scheme glued from two affine charts along a common basic open, with the two coordinates inverse to one another, admits affine opens containing any prescribed finite set of points: the chart data are exactly those of a morphism to $\mathbb{P}^1_R = \operatorname{Proj} R[x_0,x_1]$ which is an affine morphism, and the conclusion follows from the corresponding statement for schemes affine over a $\operatorname{Proj}$, [`AlgebraicGeometry.exists_isAffineOpen_forall_mem_of_isAffineHom_proj`](thm.html#AlgebraicGeometry.exists_isAffineOpen_forall_mem_of_isAffineHom_proj). It is applied to two-chart integral models of algebraic curves and, in particular, to models of the modular curves $X_1(N)$ used later in the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_finset_of_twoCharts.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_isAffineOpen_forall_mem_of_finset_of_twoCharts
    {R : Type u} [CommRing R] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of R))
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ⊔ V = ⊤)
    (f : Γ(X, U)) (g : Γ(X, V))
    (hf : U ⊓ V = X.basicOpen f) (hg : U ⊓ V = X.basicOpen g)
    (hfg : (X.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom f *
      (X.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom g = 1)
    (F : Finset X) : ∃ W : X.Opens, IsAffineOpen W ∧ ∀ x ∈ F, x ∈ W := by sorry
