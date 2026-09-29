-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_baseChange_of_locallyTrivial
-- name    : AlgebraicGeometry.Scheme.Modules.exists_linearEquiv_sections_baseChange_of_locallyTrivial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/77770062-60af-5dd4-b91d-23e0b1a4e0df
-- title:
--   Base change of sections over an affine open, locally trivial case
-- statement:
--   Let $R$ be a commutative ring, $X$ a scheme, $c : X \to \operatorname{Spec} R$ a morphism, and $M$ a sheaf of modules over the structure sheaf of $X$. Assume $M$ is locally trivial: for every point $x$ of $X$ there is an open $V \subseteq X$ with $x \in V$ such that the pullback of $M$ along the inclusion $V \hookrightarrow X$ is isomorphic, as a sheaf of modules on $V$, to the unit sheaf of modules (the structure sheaf) of $V$. Let $U \subseteq X$ be an affine open and let $A$ be a commutative $R$-algebra. Write $\operatorname{Spec} A \to \operatorname{Spec} R$ for the morphism induced by $\operatorname{algebraMap} R\,A$, and let $\mathrm{pr}_1, \mathrm{pr}_2$ be the two projections of the fibre product $X \times_{\operatorname{Spec} R} \operatorname{Spec} A$. The module $\Gamma(M, U)$ carries the $R$-module structure obtained by restricting scalars along the $R$-algebra structure on $\Gamma(X, U)$ coming from $c$ (the composite of the inverse of the $\Gamma$–$\operatorname{Spec}$ isomorphism for $R$ with the component $c^{\sharp} : \Gamma(\operatorname{Spec} R, \top) \to \Gamma(X, U)$), and $\Gamma(\mathrm{pr}_1^{*}M, \mathrm{pr}_1^{-1}U)$ carries in the same way the $A$-module structure coming from $\mathrm{pr}_2$. The assertion is that there exists an $A$-linear isomorphism
--   $$e : A \otimes_R \Gamma(M, U) \;\xrightarrow{\ \sim\ }\; \Gamma\bigl(\mathrm{pr}_1^{*}M, \mathrm{pr}_1^{-1}U\bigr)$$
--   such that for every section $m \in \Gamma(M, U)$ one has $e(1 \otimes m) = \mathrm{pr}_1^{*}(m)$, where $\mathrm{pr}_1^{*}(m)$ denotes the image of $m$ under the component over $U$ of the unit $M \to (\mathrm{pr}_1)_{*}\mathrm{pr}_1^{*}M$ of the pullback–pushforward adjunction for $\mathrm{pr}_1$.
--
--   This is the statement that formation of sections over an affine open commutes with base change, in the case of a sheaf of modules that is Zariski-locally isomorphic to the structure sheaf (for instance an invertible module). It is the input for the identification of two-chart Čech section data of a line bundle on a family of curves after base change, and is used by the results asserting that the base-change comparison map for modules is an isomorphism over an affine morphism or over a two-affine open cover.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_baseChange_of_locallyTrivial.lean

import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Mathlib.LinearAlgebra.TensorProduct.Tower

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.Scheme.Modules.exists_linearEquiv_sections_baseChange_of_locallyTrivial
    {R : Type u} [CommRing R] {X : Scheme.{u}} (c : X ⟶ Spec (.of R)) (M : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (U : X.Opens) (hU : IsAffineOpen U) (A : Type u) [CommRing A] [Algebra R A] :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c M U
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
      (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))
      ((Scheme.Modules.pullback (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).obj M)
      ((Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A)) ⁻¹ᵁ U)
    ∃ e : A ⊗[R] Γ(M, U) ≃ₗ[A]
        Γ((Scheme.Modules.pullback (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).obj M,
          (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A)) ⁻¹ᵁ U),
      ∀ m : Γ(M, U), e ((1 : A) ⊗ₜ[R] m) =
        (((Scheme.Modules.pullbackPushforwardAdjunction
          (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).unit.app M).app U).hom m := by sorry
