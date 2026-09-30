-- Prove2me | Theorems.Thm_CategoryTheory_MonoidalCategory_Effect_sum_probability_eq_one
-- name    : CategoryTheory.MonoidalCategory.Effect.sum_probability_eq_one
-- status  : Proved
-- author  : @Bingyu Xia
-- created : 2026-09-30T00:28:10.031877+00:00
-- url     : https://prove2.me/theorems/854dbe4d-66eb-4183-b4f3-421eb0a800da
-- title:
--   The Born rule: probabilities of a complete disjoint family sum to one
-- statement:
--   Let $\mathcal{C}$ be a monoidal dagger category with zero morphisms, let $a : I \to c$ be a state, and let $x : I \to \mathrm{Eff}(c)$ be a family of effects carrying a dagger biproduct. If $x$ is complete and disjoint, then the probabilities of the outcomes sum to the identity scalar: $$\sum_i \mathrm{Prob}(a, x_i) = \mathrm{id}_I ,$$ where $\mathrm{Prob}(a, x_i) = a^\dagger \circ x_i^\dagger \circ x_i \circ a$. This is the categorical Born rule, and the goal of this mission. The source states it for complete families only; disjointness is required as well, and its own proof invokes Lemma 2.52, whose hypothesis is complete *and* disjoint. Without disjointness the statement is false: in $\mathcal{C} = \mathbf{Hilb}$, take $x_1 = \langle e_1 |$ and $x_2 = \langle e_1 | + \langle e_2 |$, which are complete but not disjoint, and $a = |e_1\rangle$; the two probabilities are $1$ and $2$.
-- source:
--   Reutter & Vicary, *Categorical Quantum Mechanics*, §2.4.3, Proposition 2.55 (Born rule)
--
--   Lean source: https://github.com/BryceT233/Categorical-Quantum-Mechanics/blob/dd7d4573fabdb5ca8af0811c1af6396a49365b42/FQFP/CQM/Category/Measurement.lean#L212

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

theorem CategoryTheory.MonoidalCategory.Effect.sum_probability_eq_one {C : Type u} [CategoryTheory.Category.{v, u} C] [CategoryTheory.DaggerCategory C] [CategoryTheory.MonoidalCategory C] [CategoryTheory.Preadditive C] {ι : Type} [Fintype ι] {c : C} (x : ι → CategoryTheory.MonoidalCategory.Effect c) [CategoryTheory.Limits.HasBiproduct fun (x : ι) => CategoryTheory.MonoidalCategoryStruct.tensorUnit C] [CategoryTheory.DaggerCategory.IsDaggerBiproduct fun (x : ι) => CategoryTheory.MonoidalCategoryStruct.tensorUnit C] (hx : CategoryTheory.MonoidalCategory.Effect.Complete x) (hxd : CategoryTheory.MonoidalCategory.Effect.Disjoint x) (a : CategoryTheory.MonoidalCategory.State c) (ha : CategoryTheory.DaggerCategory.IsIsometry a) : ∑ i : ι, CategoryTheory.MonoidalCategory.probability a (x i) =
  CategoryTheory.CategoryStruct.id (CategoryTheory.MonoidalCategoryStruct.tensorUnit C) := by sorry
