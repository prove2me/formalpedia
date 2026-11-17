-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_app_ratio_tensor
-- name    : AlgebraicGeometry.Scheme.Modules.ProjPresentation.app_ratio_tensor
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:00:41.730828+00:00
-- url     : https://prove2.me/theorems/4e4f3458-2715-4c4f-a1b1-055c4fc84b28
-- title:
--   Ratio coordinates in a tensor presentation are products of the two factor ratios
-- statement:
--   Let $P$ and $Q$ be projective presentations of modules $L$ and $M$, and let $R$ be a presentation of $L⊗M$ whose coordinates are indexed by pairs, with sections equal to tensor products. If $idx(k)=(i_k,j_k)$, then on any open contained in the relevant charts, $$r^R_{k,l}=r^P_{i_k,i_l}\,r^Q_{j_k,j_l}.$$ This is the local Segre-coordinate identity underlying tensor-product heights.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation

set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.ProjPresentation

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.app_ratio_tensor
    {K : Type} [Field K] {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of K)}
    {L M : X.Modules} {N N' : ℕ}
    (P : L.ProjPresentation f N) (Q : M.ProjPresentation f N')
    (idx : Fin (N * N' + N + N' + 1) ≃ Fin (N + 1) × Fin (N' + 1))
    (R : (L ⊗ M).ProjPresentation f (N * N' + N + N'))
    (hσ : ∀ k, R.σ k = Scheme.Modules.tensorSections (P.σ (idx k).1) (Q.σ (idx k).2))
    (k l : Fin (N * N' + N + N' + 1))
    (W : X.Opens)
    (hP : W ≤ P.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X (idx k).1))
    (hQ : W ≤ Q.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X (idx k).2))
    (hR : W ≤ R.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X k)) :
    X.presheaf.map (homOfLE hR).op
      (R.toProj.app (Proj.basicOpen _ (MvPolynomial.X k))
        (Proj.awayToSection _ (MvPolynomial.X k) (ProjSpace.ratio K _ k l))) =
    X.presheaf.map (homOfLE hP).op
      (P.toProj.app (Proj.basicOpen _ (MvPolynomial.X (idx k).1))
        (Proj.awayToSection _ (MvPolynomial.X (idx k).1)
          (ProjSpace.ratio K _ (idx k).1 (idx l).1))) *
    X.presheaf.map (homOfLE hQ).op
      (Q.toProj.app (Proj.basicOpen _ (MvPolynomial.X (idx k).2))
        (Proj.awayToSection _ (MvPolynomial.X (idx k).2)
          (ProjSpace.ratio K _ (idx k).2 (idx l).2))) := by sorry
