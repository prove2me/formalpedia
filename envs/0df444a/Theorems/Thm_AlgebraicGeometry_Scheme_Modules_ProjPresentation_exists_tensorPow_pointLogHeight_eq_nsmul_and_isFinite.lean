-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_tensorPow_pointLogHeight_eq_nsmul_and_isFinite
-- name    : AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_tensorPow_pointLogHeight_eq_nsmul_and_isFinite
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:14:16.201558+00:00
-- url     : https://prove2.me/theorems/6f9a92f3-067b-419b-a6d9-0e112efba185
-- title:
--   A positive tensor power has a finite presentation with height multiplied by the exponent
-- statement:
--   Let $P$ be a finite projective presentation of a module $M$ over a number field, and let $n>0$. There exists a finite presentation $R_n$ of $M^{⊗n}$ such that for every rational point $x$, $$h_{R_n}(x)=n\,h_P(x).$$ This realizes the quadratic line-bundle identities as exact height scaling statements.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjPresentationHeight
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top
import Definitions.Def_AlgebraicGeometry_ProjSpacePoints
import Definitions.Def_AlgebraicGeometry_ProjSpaceEquivalence
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation

set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.ProjPresentation

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_tensorPow_pointLogHeight_eq_nsmul_and_isFinite
    {K : Type} [Field K] [NumberField K] {X : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of K)} {M : X.Modules} {N : ℕ}
    (P : M.ProjPresentation f N) (hP : IsFinite P.toProj) (n : ℕ) (hn : 0 < n) :
    ∃ (Nn : ℕ) (Rn : (M.tensorPow n).ProjPresentation f Nn),
      IsFinite Rn.toProj ∧ ∀ x : Scheme.KPoint f,
        Rn.pointLogHeight x = n * P.pointLogHeight x := by sorry
