-- Prove2me | Theorems.Thm_CategoryTheory_DaggerCategory_dagger_entry
-- name    : CategoryTheory.DaggerCategory.dagger_entry
-- status  : Proved
-- author  : @Bingyu Xia
-- created : 2026-09-30T00:27:45.742018+00:00
-- url     : https://prove2.me/theorems/53646202-7753-4ab6-9be5-e543daa26619
-- title:
--   The dagger of a morphism of biproducts daggers every entry
-- statement:
--   Let $\mathcal{C}$ be a dagger category with zero morphisms, let $f : I \to \mathcal{C}$ and $G : J \to \mathcal{C}$ be finite families carrying dagger biproducts, and let $x : \bigoplus_i f_i \to \bigoplus_j G_j$. Writing $x_{ij}$ for the $(i,j)$ entry of $x$, $$(x^\dagger)_{ji} = (x_{ij})^\dagger .$$ In other words, transposing a matrix of morphisms daggers each of its entries. This is the intrinsic, universe-polymorphic form; see `dagger_biproduct_matrix` for the version stated with `biproduct.matrix`.
-- source:
--   Reutter & Vicary, *Categorical Quantum Mechanics*, §2.3.3, Lemma 2.41
--
--   Lean source: https://github.com/BryceT233/Categorical-Quantum-Mechanics/blob/dd7d4573fabdb5ca8af0811c1af6396a49365b42/FQFP/CQM/Category/DaggerBiproduct.lean#L88

import Definitions.Def_CQM_DaggerCategory
import Definitions.Def_CQM_DaggerBiproduct
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Preadditive.Biproducts

open CategoryTheory Limits
open CategoryTheory.DaggerCategory
universe u u_1 u_2 v

theorem CategoryTheory.DaggerCategory.dagger_entry {C : Type u} [CategoryTheory.Category.{v, u} C] [CategoryTheory.DaggerCategory C] [CategoryTheory.Limits.HasZeroMorphisms C] {ι : Type u_1} {f : ι → C} [CategoryTheory.Limits.HasBiproduct f] [CategoryTheory.DaggerCategory.IsDaggerBiproduct f] {κ : Type u_2} {G : κ → C} [CategoryTheory.Limits.HasBiproduct G] [CategoryTheory.DaggerCategory.IsDaggerBiproduct G] (x : ⨁ f ⟶ ⨁ G) (i : ι) (j : κ) : CategoryTheory.DaggerCategory.entry x† j i = (CategoryTheory.DaggerCategory.entry x i j)† := by sorry
