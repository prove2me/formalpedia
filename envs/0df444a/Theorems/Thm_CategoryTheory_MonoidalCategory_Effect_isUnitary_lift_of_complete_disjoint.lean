-- Prove2me | Theorems.Thm_CategoryTheory_MonoidalCategory_Effect_isUnitary_lift_of_complete_disjoint
-- name    : CategoryTheory.MonoidalCategory.Effect.isUnitary_lift_of_complete_disjoint
-- status  : Proved
-- author  : @Bingyu Xia
-- created : 2026-09-30T00:28:07.536812+00:00
-- url     : https://prove2.me/theorems/071a6b74-8a9a-4666-96d1-b6e7bf2ed4ed
-- title:
--   A complete disjoint family of effects lifts to a unitary
-- statement:
--   Let $\mathcal{C}$ be a monoidal dagger category with zero morphisms and let $x : I \to \mathrm{Eff}(c)$ be a family of effects carrying a dagger biproduct. If $x$ is both complete and disjoint, then its lift $$\langle x \rangle : \bigoplus_i I \longrightarrow c$$ is a unitary, that is $\langle x \rangle^\dagger \circ \langle x \rangle = \mathrm{id}$ and $\langle x \rangle \circ \langle x \rangle^\dagger = \mathrm{id}$. The source states this under an additional hypothesis of equalizers; that hypothesis is not needed here, since completeness alone already forces $y = 0$ from $y \circ \langle x \rangle = 0$, so the statement below is strictly stronger than the book's.
-- source:
--   Reutter & Vicary, *Categorical Quantum Mechanics*, §2.4.3, Lemma 2.53
--
--   Lean source: https://github.com/BryceT233/Categorical-Quantum-Mechanics/blob/dd7d4573fabdb5ca8af0811c1af6396a49365b42/FQFP/CQM/Category/Measurement.lean#L167

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

theorem CategoryTheory.MonoidalCategory.Effect.isUnitary_lift_of_complete_disjoint {C : Type u} [CategoryTheory.Category.{v, u} C] [CategoryTheory.DaggerCategory C] [CategoryTheory.MonoidalCategory C] [CategoryTheory.Preadditive C] {ι : Type} {c : C} (x : ι → CategoryTheory.MonoidalCategory.Effect c) [CategoryTheory.Limits.HasBiproduct fun (x : ι) => CategoryTheory.MonoidalCategoryStruct.tensorUnit C] [CategoryTheory.DaggerCategory.IsDaggerBiproduct fun (x : ι) => CategoryTheory.MonoidalCategoryStruct.tensorUnit C] (hx : CategoryTheory.MonoidalCategory.Effect.Complete x) (hxd : CategoryTheory.MonoidalCategory.Effect.Disjoint x) : CategoryTheory.DaggerCategory.IsUnitary (CategoryTheory.Limits.biproduct.lift x) := by sorry
