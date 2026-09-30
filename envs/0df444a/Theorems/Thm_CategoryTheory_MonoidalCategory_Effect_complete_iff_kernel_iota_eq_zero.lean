-- Prove2me | Theorems.Thm_CategoryTheory_MonoidalCategory_Effect_complete_iff_kernel_iota_eq_zero
-- name    : CategoryTheory.MonoidalCategory.Effect.complete_iff_kernel_iota_eq_zero
-- status  : Proved
-- author  : @Bingyu Xia
-- created : 2026-09-30T00:28:04.196783+00:00
-- url     : https://prove2.me/theorems/28a2675d-eef0-43c8-8c5d-5680ddf5cb2c
-- title:
--   A family of effects is complete iff the kernel of its lift is trivial
-- statement:
--   Let $\mathcal{C}$ be a monoidal category with zero morphisms, let $x : I \to \mathrm{Eff}(c)$ be a family of effects carrying a biproduct, and let $\iota : \bigoplus_i I \to c$ be the induced map (the lift of $x$ into $c$). Then $$x \text{ is complete} \iff \ker(\iota) = 0 .$$ Completeness is the condition $\bigvee_i x_i = \mathrm{id}_c$; the content of the lemma is that it is detected on the biproduct of the units.
-- source:
--   Reutter & Vicary, *Categorical Quantum Mechanics*, §2.4.3, Lemma 2.52 (completeness half)
--
--   Lean source: https://github.com/BryceT233/Categorical-Quantum-Mechanics/blob/dd7d4573fabdb5ca8af0811c1af6396a49365b42/FQFP/CQM/Category/Measurement.lean#L132

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

theorem CategoryTheory.MonoidalCategory.Effect.complete_iff_kernel_iota_eq_zero {C : Type u} [CategoryTheory.Category.{v, u} C] [CategoryTheory.MonoidalCategory C] [CategoryTheory.Limits.HasZeroMorphisms C] {ι : Type} {c : C} (x : ι → CategoryTheory.MonoidalCategory.Effect c) [CategoryTheory.Limits.HasBiproduct fun (x : ι) => CategoryTheory.MonoidalCategoryStruct.tensorUnit C] [CategoryTheory.Limits.HasKernel (CategoryTheory.Limits.biproduct.lift x)] : CategoryTheory.MonoidalCategory.Effect.Complete x ↔
  CategoryTheory.Limits.kernel.ι (CategoryTheory.Limits.biproduct.lift x) = 0 := by sorry
