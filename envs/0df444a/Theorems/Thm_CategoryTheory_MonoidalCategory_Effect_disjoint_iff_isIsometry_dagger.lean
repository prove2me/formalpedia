-- Prove2me | Theorems.Thm_CategoryTheory_MonoidalCategory_Effect_disjoint_iff_isIsometry_dagger
-- name    : CategoryTheory.MonoidalCategory.Effect.disjoint_iff_isIsometry_dagger
-- status  : Proved
-- author  : @Bingyu Xia
-- created : 2026-09-30T00:28:01.242675+00:00
-- url     : https://prove2.me/theorems/eb38102b-42e5-443d-869e-62fc6fc5a03e
-- title:
--   A family of effects is disjoint iff the dagger of its lift is an isometry
-- statement:
--   Let $\mathcal{C}$ be a monoidal dagger category with zero morphisms, let $x : I \to \mathrm{Eff}(c)$ be a family of effects on $c$ carrying a dagger biproduct, and let $\langle x \rangle = \mathrm{lift}(x) : \bigoplus_i I \to c$ be the induced map out of the biproduct of the unit objects. Then $$x \text{ is disjoint} \iff \langle x \rangle^\dagger \text{ is an isometry},$$ i.e. $\langle x \rangle^\dagger \circ \langle x \rangle = \mathrm{id}_{\bigoplus_i I}$. Note the dagger: it is the dagger of the lift, not the lift itself, that is an isometry.
-- source:
--   Reutter & Vicary, *Categorical Quantum Mechanics*, §2.4.3, Lemma 2.52 (disjointness half)
--
--   Lean source: https://github.com/BryceT233/Categorical-Quantum-Mechanics/blob/dd7d4573fabdb5ca8af0811c1af6396a49365b42/FQFP/CQM/Category/Measurement.lean#L86

import Definitions.Def_CQM_DaggerCategory
import Definitions.Def_CQM_DaggerBiproduct
import Definitions.Def_CQM_MonoidalCategory
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.CategoryTheory.Preadditive.Basic

open CategoryTheory Limits
open scoped BigOperators
open CategoryTheory.DaggerCategory
open CategoryTheory.MonoidalCategory
universe u v

theorem CategoryTheory.MonoidalCategory.Effect.disjoint_iff_isIsometry_dagger {C : Type u} [CategoryTheory.Category.{v, u} C] [CategoryTheory.DaggerCategory C] [CategoryTheory.MonoidalCategory C] [CategoryTheory.Limits.HasZeroMorphisms C] {ι : Type} {c : C} (x : ι → CategoryTheory.MonoidalCategory.Effect c) [CategoryTheory.Limits.HasBiproduct fun (x : ι) => CategoryTheory.MonoidalCategoryStruct.tensorUnit C] [CategoryTheory.DaggerCategory.IsDaggerBiproduct fun (x : ι) => CategoryTheory.MonoidalCategoryStruct.tensorUnit C] : CategoryTheory.MonoidalCategory.Effect.Disjoint x ↔
  CategoryTheory.DaggerCategory.IsIsometry (CategoryTheory.Limits.biproduct.lift x)† := by sorry
