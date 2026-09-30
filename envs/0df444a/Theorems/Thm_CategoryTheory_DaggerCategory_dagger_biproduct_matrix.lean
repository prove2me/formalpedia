-- Prove2me | Theorems.Thm_CategoryTheory_DaggerCategory_dagger_biproduct_matrix
-- name    : CategoryTheory.DaggerCategory.dagger_biproduct_matrix
-- status  : Proved
-- author  : @Bingyu Xia
-- created : 2026-09-30T00:27:55.973577+00:00
-- url     : https://prove2.me/theorems/e9183ba5-dc88-428d-97e4-d2a37baee0b7
-- title:
--   The dagger of a matrix is the conjugate transpose
-- statement:
--   Let $\mathcal{C}$ be a dagger category with finite biproducts, and let $m_{ij} : F_i \to G_j$ be a matrix of morphisms indexed by finite types. Then $$\left(\begin{pmatrix} m_{ij} \end{pmatrix}\right)^\dagger = \begin{pmatrix} (m_{ji})^\dagger \end{pmatrix},$$ that is, the dagger of the matrix $(m_{ij})$ is the matrix whose $(i,j)$ entry is $(m_{ji})^\dagger$. Mathlib's `biproduct.matrix` is monomorphic in its index types, so this statement is made at `Type 0`.
-- source:
--   Reutter & Vicary, *Categorical Quantum Mechanics*, §2.3.3, Lemma 2.41
--
--   Lean source: https://github.com/BryceT233/Categorical-Quantum-Mechanics/blob/dd7d4573fabdb5ca8af0811c1af6396a49365b42/FQFP/CQM/Category/DaggerBiproduct.lean#L102

import Definitions.Def_CQM_DaggerCategory
import Definitions.Def_CQM_DaggerBiproduct
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Preadditive.Biproducts

open CategoryTheory Limits
open CategoryTheory.DaggerCategory
universe u v

theorem CategoryTheory.DaggerCategory.dagger_biproduct_matrix {C : Type u} [CategoryTheory.Category.{v, u} C] [CategoryTheory.DaggerCategory C] [CategoryTheory.Limits.HasZeroMorphisms C] {ι : Type} {κ : Type} [Finite ι] [Finite κ] {F : ι → C} {G : κ → C} [CategoryTheory.Limits.HasFiniteBiproducts C] [CategoryTheory.DaggerCategory.IsDaggerBiproduct F] [CategoryTheory.DaggerCategory.IsDaggerBiproduct G] (m : (i : ι) → (j : κ) → F i ⟶ G j) : (CategoryTheory.Limits.biproduct.matrix m)† = CategoryTheory.Limits.biproduct.matrix fun (j : κ) (i : ι) => (m i j)† := by sorry
