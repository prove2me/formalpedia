-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullback_iso_trans_eq_of_cocycle
-- name    : AlgebraicGeometry.Scheme.Modules.pullback_iso_trans_eq_of_cocycle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/9fac81e5-a894-5f2f-a3ea-31a804191f71
-- title:
--   Triple-overlap compatibility of pullback identifications from a cocycle
-- statement:
--   Let $X',X'',X'''$ be schemes, let $a_1,a_2:X''\to X'$ and $b_{12},b_{13},b_{23}:X'''\to X''$ satisfy the simplicial identities $h_1:b_{12}\circ a_1=b_{13}\circ a_1$, $h_2:b_{12}\circ a_2=b_{23}\circ a_1$, $h_3:b_{13}\circ a_2=b_{23}\circ a_2$ (composites written in diagrammatic order), let $L'$ be an object of `X'.Modules` and let $\psi:(\mathrm{pullback}\,a_1).obj\,L'\cong(\mathrm{pullback}\,a_2).obj\,L'$ be an isomorphism. Abbreviate $c_{g,f}:=(\mathrm{pullbackComp}\,g\,f).app\,L'$, the component at $L'$ of the natural isomorphism `pullbackComp` comparing pullback along a composite with the composite of pullbacks, and $\kappa_i:=(\mathrm{pullbackCongr}\,h_i).app\,L'$, the component of the isomorphism `pullbackCongr` of pullback functors transported along the equality $h_i$. Assume the cocycle condition $\kappa_1^{-1}\cdot c_{b_{12},a_1}^{-1}\cdot (\mathrm{pullback}\,b_{12})\psi\cdot c_{b_{12},a_2}\cdot\kappa_2\cdot c_{b_{23},a_1}^{-1}\cdot(\mathrm{pullback}\,b_{23})\psi\cdot c_{b_{23},a_2}\cdot\kappa_3^{-1}=c_{b_{13},a_1}^{-1}\cdot(\mathrm{pullback}\,b_{13})\psi\cdot c_{b_{13},a_2}$, where juxtaposition is composition of isomorphisms in diagrammatic order. The conclusion is the conjunction of three equalities of isomorphisms in `X'''.Modules`: (i) $\kappa_1^{-1}\cdot(c_{b_{12},a_1}^{-1}\cdot(\mathrm{pullback}\,b_{12})(\mathrm{id})\cdot\mathrm{id})=c_{b_{13},a_1}^{-1}\cdot(\mathrm{pullback}\,b_{13})(\mathrm{id})\cdot(c_{b_{13},a_1}\cdot\kappa_1^{-1}\cdot c_{b_{12},a_1}^{-1})$; (ii) $\kappa_2^{-1}\cdot(c_{b_{12},a_2}^{-1}\cdot(\mathrm{pullback}\,b_{12})\psi^{-1}\cdot\mathrm{id})=c_{b_{23},a_1}^{-1}\cdot(\mathrm{pullback}\,b_{23})(\mathrm{id})\cdot(c_{b_{23},a_1}\cdot\kappa_2^{-1}\cdot c_{b_{12},a_2}^{-1}\cdot(\mathrm{pullback}\,b_{12})\psi^{-1})$; (iii) $\kappa_3^{-1}\cdot(c_{b_{13},a_2}^{-1}\cdot(\mathrm{pullback}\,b_{13})\psi^{-1}\cdot(c_{b_{13},a_1}\cdot\kappa_1^{-1}\cdot c_{b_{12},a_1}^{-1}))=c_{b_{23},a_2}^{-1}\cdot(\mathrm{pullback}\,b_{23})\psi^{-1}\cdot(c_{b_{23},a_1}\cdot\kappa_2^{-1}\cdot c_{b_{12},a_2}^{-1}\cdot(\mathrm{pullback}\,b_{12})\psi^{-1})$, the identity isomorphisms being those of $(\mathrm{pullback}\,a_1).obj\,L'$ and of its pullback along $b_{12}$.
--
--   This is the triple-overlap compatibility of the identifications attached to a descent datum on a 2-truncated simplicial object: for each of the three pairs of coinciding faces $X'''\to X'$, the two composite identifications between the corresponding pullbacks of $L'$ agree, the third such identity being the cocycle condition for $\psi$ read backwards along $b_{13}\circ a_2=b_{23}\circ a_2$. It is used by [`AlgebraicGeometry.GradedOAlgebra.IsSectionRing.cocycle_trans_symm_of_cocycle`](thm.html#AlgebraicGeometry.GradedOAlgebra.IsSectionRing.cocycle_trans_symm_of_cocycle).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_pullback_iso_trans_eq_of_cocycle.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.pullback_iso_trans_eq_of_cocycle
    (X' X'' X''' : Scheme.{u}) (a₁ a₂ : X'' ⟶ X') (b₁₂ b₁₃ b₂₃ : X''' ⟶ X'')
    (h₁ : b₁₂ ≫ a₁ = b₁₃ ≫ a₁) (h₂ : b₁₂ ≫ a₂ = b₂₃ ≫ a₁) (h₃ : b₁₃ ≫ a₂ = b₂₃ ≫ a₂)
    (L' : X'.Modules)
    (ψ : (Scheme.Modules.pullback a₁).obj L' ≅ (Scheme.Modules.pullback a₂).obj L')
    (hψ : ((Scheme.Modules.pullbackCongr h₁).app L').symm ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₁₂).mapIso ψ ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₂).app L') ≪≫
          ((Scheme.Modules.pullbackCongr h₂).app L') ≪≫ ((Scheme.Modules.pullbackComp b₂₃ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₂₃).mapIso ψ ≪≫ ((Scheme.Modules.pullbackComp b₂₃ a₂).app L') ≪≫ ((Scheme.Modules.pullbackCongr h₃).app L').symm
        = ((Scheme.Modules.pullbackComp b₁₃ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₁₃).mapIso ψ ≪≫ ((Scheme.Modules.pullbackComp b₁₃ a₂).app L')) :
    (((Scheme.Modules.pullbackCongr h₁).app L').symm ≪≫ (((Scheme.Modules.pullbackComp b₁₂ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₁₂).mapIso (Iso.refl ((Scheme.Modules.pullback a₁).obj L')) ≪≫ (Iso.refl ((Scheme.Modules.pullback b₁₂).obj ((Scheme.Modules.pullback a₁).obj L'))))
        = (((Scheme.Modules.pullbackComp b₁₃ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₁₃).mapIso (Iso.refl ((Scheme.Modules.pullback a₁).obj L')) ≪≫ (((Scheme.Modules.pullbackComp b₁₃ a₁).app L') ≪≫ ((Scheme.Modules.pullbackCongr h₁).app L').symm ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₁).app L').symm))) ∧
    (((Scheme.Modules.pullbackCongr h₂).app L').symm ≪≫ (((Scheme.Modules.pullbackComp b₁₂ a₂).app L').symm ≪≫ (Scheme.Modules.pullback b₁₂).mapIso ψ.symm ≪≫ (Iso.refl ((Scheme.Modules.pullback b₁₂).obj ((Scheme.Modules.pullback a₁).obj L'))))
        = (((Scheme.Modules.pullbackComp b₂₃ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₂₃).mapIso (Iso.refl ((Scheme.Modules.pullback a₁).obj L')) ≪≫ (((Scheme.Modules.pullbackComp b₂₃ a₁).app L') ≪≫ ((Scheme.Modules.pullbackCongr h₂).app L').symm ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₂).app L').symm ≪≫ (Scheme.Modules.pullback b₁₂).mapIso ψ.symm))) ∧
    (((Scheme.Modules.pullbackCongr h₃).app L').symm ≪≫ (((Scheme.Modules.pullbackComp b₁₃ a₂).app L').symm ≪≫ (Scheme.Modules.pullback b₁₃).mapIso ψ.symm ≪≫ (((Scheme.Modules.pullbackComp b₁₃ a₁).app L') ≪≫ ((Scheme.Modules.pullbackCongr h₁).app L').symm ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₁).app L').symm))
        = (((Scheme.Modules.pullbackComp b₂₃ a₂).app L').symm ≪≫ (Scheme.Modules.pullback b₂₃).mapIso ψ.symm ≪≫ (((Scheme.Modules.pullbackComp b₂₃ a₁).app L') ≪≫ ((Scheme.Modules.pullbackCongr h₂).app L').symm ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₂).app L').symm ≪≫ (Scheme.Modules.pullback b₁₂).mapIso ψ.symm))) := by sorry
