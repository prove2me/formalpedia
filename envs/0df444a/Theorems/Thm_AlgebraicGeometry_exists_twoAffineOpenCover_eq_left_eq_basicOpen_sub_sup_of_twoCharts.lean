-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_twoAffineOpenCover_eq_left_eq_basicOpen_sub_sup_of_twoCharts
-- name    : AlgebraicGeometry.exists_twoAffineOpenCover_eq_left_eq_basicOpen_sub_sup_of_twoCharts
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/72f8c6c4-173f-58e9-89b9-430de30acc28
-- title:
--   Two-affine cover by U and the locus t ≠ s
-- statement:
--   Let $X$ be a scheme and let $U, V$ be open subsets of $X$, both assumed affine open, let $f \in \Gamma(X, U)$ and $g \in \Gamma(X, V)$, and assume that the intersection $U \cap V$ equals both the basic open subset $X_f$ cut out by $f$ on $U$ and the basic open subset $X_g$ cut out by $g$ on $V$, that the product of the restrictions of $f$ and of $g$ along $U \cap V \le U$ and $U \cap V \le V$ is the unit section of $\Gamma(X, U \cap V)$, and that $U \cup V = X$ (i.e. $U \sqcup V = \top$ in the lattice of opens). Let further $s \in \Gamma(X, X)$ be a global section. The conclusion asserts the existence of a structure consisting of two open subsets $\mathcal{W}.U_0$ and $\mathcal{W}.U_1$ of $X$, each affine open, whose union is all of $X$ and whose intersection is again affine open, such that $\mathcal{W}.U_0 = U$ and $\mathcal{W}.U_1$ is the union of the basic open subset of $U$ defined by $f - s|_U$ and the basic open subset of $V$ defined by $1 - s|_V \cdot g$.
--
--   In the situation of two affine charts glued along $U \cap V$ with coordinates $f$ on $U$ and $g = f^{-1}$ on $V$, which is the chart data of a morphism $X \to \mathbb{P}^1$, the statement exhibits $X$ as covered by the chart $U$ (the locus $t \ne \infty$) together with the locus $t \ne s$, in such a way that both members and their intersection are affine. It is used in the construction of two-affine open covers attached to the Deligne–Rapoport model package for modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_twoAffineOpenCover_eq_left_eq_basicOpen_sub_sup_of_twoCharts.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_twoAffineOpenCover_eq_left_eq_basicOpen_sub_sup_of_twoCharts
    {X : Scheme.{u}} (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (f : Γ(X, U)) (g : Γ(X, V))
    (hf : U ⊓ V = X.basicOpen f) (hg : U ⊓ V = X.basicOpen g)
    (hfg : (X.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom f *
      (X.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom g = 1)
    (hUV : U ⊔ V = ⊤) (s : Γ(X, ⊤)) :
    ∃ 𝒲 : X.TwoAffineOpenCover,
      𝒲.U0 = U ∧
      𝒲.U1 = X.basicOpen (f - (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom s) ⊔
        X.basicOpen (1 - (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom s * g) := by sorry
