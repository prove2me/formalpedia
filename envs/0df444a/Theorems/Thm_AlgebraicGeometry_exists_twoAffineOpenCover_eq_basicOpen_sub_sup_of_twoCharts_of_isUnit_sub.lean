-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_twoAffineOpenCover_eq_basicOpen_sub_sup_of_twoCharts_of_isUnit_sub
-- name    : AlgebraicGeometry.exists_twoAffineOpenCover_eq_basicOpen_sub_sup_of_twoCharts_of_isUnit_sub
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/1eb435aa-d546-5e24-952a-75cdaa10df14
-- title:
--   Loci t ≠ s₀, t ≠ s₁ give a two-affine cover
-- statement:
--   Let $X$ be a scheme, let $U,V$ be open subsets of $X$ that are affine opens, and let $f \in \Gamma(X,U)$ and $g \in \Gamma(X,V)$ be sections of the structure sheaf over $U$ and $V$ respectively. Assume the chart compatibilities $U \cap V = X_f$ and $U \cap V = X_g$, where $X_h$ denotes the basic open locus of a section $h$, that the product of the restriction of $f$ to $U \cap V$ with the restriction of $g$ to $U \cap V$ equals $1$, and that $U \cup V = \top$. Let $s_0, s_1 \in \Gamma(X,\top)$ be global sections whose difference $s_0 - s_1$ is a unit. Then there exists a structure consisting of two affine opens $W_0, W_1$ of $X$ with $W_0 \cup W_1 = \top$ and with $W_0 \cap W_1$ again an affine open, such that, writing $s_i|_U$ and $s_i|_V$ for the restrictions of the global sections along $U \le \top$ and $V \le \top$, one has $W_0 = X_{f - s_0|_U} \cup X_{1 - s_0|_V\, g}$ and $W_1 = X_{f - s_1|_U} \cup X_{1 - s_1|_V\, g}$.
--
--   The hypotheses are the chart data of a coordinate $t$ on $X$ with $t|_U = f$ and $t|_V = g^{-1}$, and the two opens produced are the loci $t \neq s_0$ and $t \neq s_1$; the statement records that these two loci, their union and their intersection are affine and cover $X$. It is used in the construction of the Deligne–Rapoport type model data, in [`ModularCurve.DRModelPackage.exists_twoAffineOpenCover_compl_eq_pair_compInf_compZero`](thm.html#ModularCurve.DRModelPackage.exists_twoAffineOpenCover_compl_eq_pair_compInf_compZero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_twoAffineOpenCover_eq_basicOpen_sub_sup_of_twoCharts_of_isUnit_sub.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_twoAffineOpenCover_eq_basicOpen_sub_sup_of_twoCharts_of_isUnit_sub
    {X : Scheme.{u}} (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (f : Γ(X, U)) (g : Γ(X, V))
    (hf : U ⊓ V = X.basicOpen f) (hg : U ⊓ V = X.basicOpen g)
    (hfg : (X.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom f *
      (X.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom g = 1)
    (hUV : U ⊔ V = ⊤) (s₀ s₁ : Γ(X, ⊤)) (hs : IsUnit (s₀ - s₁)) :
    ∃ 𝒲 : X.TwoAffineOpenCover,
      𝒲.U0 = X.basicOpen (f - (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom s₀) ⊔
        X.basicOpen (1 - (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom s₀ * g) ∧
      𝒲.U1 = X.basicOpen (f - (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom s₁) ⊔
        X.basicOpen (1 - (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom s₁ * g) := by sorry
