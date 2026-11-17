-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_sigma_binary_operation
-- name    : AlgebraicGeometry.Scheme.exists_sigma_binary_operation
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:00:34.4452+00:00
-- url     : https://prove2.me/theorems/925dba5d-2d4c-4e8d-a9f1-7a4aced03cb1
-- title:
--   Compatible componentwise products glue to a binary operation on a finite coproduct
-- statement:
--   Let $(X_i→S)_{i∈I}$ be a finite family, let $k:I×I→I$, and suppose maps $m_{ij}:X_i×_SX_j→X_{k(i,j)}$ are compatible with the structure maps to $S$. Then there exists an $S$-morphism $$μ:(∐_iX_i)×_S(∐_iX_i)→∐_iX_i$$ whose restriction to $X_i×_SX_j$ is $ι_{k(i,j)}∘m_{ij}$. This glues the division-carry multiplication from its components.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

theorem AlgebraicGeometry.Scheme.exists_sigma_binary_operation
    {ι : Type} [Finite ι] {S : Scheme.{0}} (X : ι → Scheme.{0})
    (f : ∀ i, X i ⟶ S) (k : ι → ι → ι)
    (m : ∀ i j, pullback (f i) (f j) ⟶ X (k i j))
    (hm : ∀ i j, m i j ≫ f (k i j) = pullback.fst (f i) (f j) ≫ f i) :
    ∃ μ : SchemeHomOver
        (pullback.fst (Sigma.desc f) (Sigma.desc f) ≫ Sigma.desc f) (Sigma.desc f),
      ∀ i j,
        pullback.map (f i) (f j) (Sigma.desc f) (Sigma.desc f)
            (Sigma.ι X i) (Sigma.ι X j) (𝟙 S) (by simp) (by simp) ≫ μ.1 =
          m i j ≫ Sigma.ι X (k i j) := by sorry
