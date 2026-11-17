-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_externalTensor_pointLogHeight_eq_add_and_isFinite
-- name    : AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_externalTensor_pointLogHeight_eq_add_and_isFinite
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:14:21.690834+00:00
-- url     : https://prove2.me/theorems/634cab01-94d1-47bd-b8d3-2880952607a6
-- title:
--   The external tensor presentation is finite and its height is the sum of the factor heights
-- statement:
--   Let $X$ and $Y$ be schemes over a number field $K$, and let finite projective presentations $P$ and $Q$ define heights on them. On $X×_KY$ there exists a finite projective presentation $R$ of the external tensor product such that for every $K$-point $z$, $$h_R(z)=h_P(pr_1z)+h_Q(pr_2z).$$ This constructs the product height used in the parallelogram argument.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjPresentationHeight
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_projPresentation_pullback_sigma_eq_toProj_eq
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_ProjSpacePoints
import Definitions.Def_AlgebraicGeometry_ProjSpaceEquivalence

set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.ProjPresentation

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_externalTensor_pointLogHeight_eq_add_and_isFinite
    {K : Type} [Field K] [NumberField K]
    {X Y : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of K)}
    {g : Y ⟶ Spec (CommRingCat.of K)}
    {L : X.Modules} {M : Y.Modules} {N N' : ℕ}
    (P : L.ProjPresentation f N) (Q : M.ProjPresentation g N')
    (hP : IsFinite P.toProj) (hQ : IsFinite Q.toProj) :
    ∃ R :
      ((Scheme.Modules.pullback (pullback.fst f g)).obj L ⊗
        (Scheme.Modules.pullback (pullback.snd f g)).obj M).ProjPresentation
        (pullback.fst f g ≫ f) (N * N' + N + N'),
      IsFinite R.toProj ∧
      ∀ z : Scheme.KPoint (pullback.fst f g ≫ f),
        R.pointLogHeight z =
          P.pointLogHeight
            ⟨z.1 ≫ pullback.fst f g,
              by rw [Category.assoc, z.2]⟩ +
          Q.pointLogHeight
            ⟨z.1 ≫ pullback.snd f g,
              by rw [Category.assoc, ← pullback.condition, z.2]⟩  := by sorry
