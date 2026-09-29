-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_finrank_sections_pullback_obj_unit_eq
-- name    : AlgebraicGeometry.Scheme.Modules.finrank_sections_pullback_obj_unit_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/1f6d6f73-8c28-5f2f-8d26-1ade55cce340
-- title:
--   Global sections of pr₁^*mathcal O_X versus mathcal O_{X_A}
-- statement:
--   Let $R$ be a commutative ring, $X$ a scheme, $f \colon X \to \operatorname{Spec} R$ a morphism, and $A$ a commutative $R$-algebra. Form the fibre product $X_A = X \times_{\operatorname{Spec} R} \operatorname{Spec} A$ along $f$ and the morphism $\operatorname{Spec}(A) \to \operatorname{Spec}(R)$ induced by the structure map $R \to A$, with projections $\mathrm{pr}_1 \colon X_A \to X$ and $\mathrm{pr}_2 \colon X_A \to \operatorname{Spec} A$. Consider the $\mathcal O_{X_A}$-module $\mathrm{pr}_1^{*}\mathcal O_X$, the pullback along $\mathrm{pr}_1$ of the unit module of the sheaf of rings of $X$. Both $\Gamma(X_A, \mathrm{pr}_1^{*}\mathcal O_X)$ and $\Gamma(X_A, \mathcal O_{X_A})$ are regarded as $A$-modules through $\mathrm{pr}_2$: the ring map $A \to \Gamma(X_A, \mathcal O_{X_A})$ obtained from $\mathrm{pr}_2$ on global sections (via the inverse of the $\Gamma$–$\operatorname{Spec}$ adjunction isomorphism for $A$) makes $\Gamma(X_A, \mathcal O_{X_A})$ an $A$-algebra, and the module of sections of $\mathrm{pr}_1^{*}\mathcal O_X$ becomes an $A$-module by restriction of scalars along that map. The assertion is twofold: $\Gamma(X_A, \mathrm{pr}_1^{*}\mathcal O_X)$ is a finite $A$-module if and only if $\Gamma(X_A, \mathcal O_{X_A})$ is, and the two $A$-ranks (`Module.finrank`) agree.
--
--   This records the comparison, over a base change of a scheme along $R \to A$, between the global sections of the pulled-back structure sheaf and the global functions on the base-changed scheme, as $A$-modules. It serves as a bridge between statements phrased in terms of module pullbacks and statements phrased in terms of $\Gamma(X_A, \mathcal O_{X_A})$, and is used in the proof that the locus of points of $\operatorname{Spec} A$ with irreducible fibre is open for a proper smooth morphism over a Noetherian base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_finrank_sections_pullback_obj_unit_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Modules.finrank_sections_pullback_obj_unit_eq
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (A : Type u) [CommRing A] [Algebra R A] :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
      (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap R A))
      ((Scheme.Modules.pullback (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A))).obj
        (SheafOfModules.unit X.ringCatSheaf)) ⊤
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
    (Module.Finite A Γ((Scheme.Modules.pullback (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A))).obj
        (SheafOfModules.unit X.ringCatSheaf), ⊤) ↔
      Module.Finite A Γ(Limits.pullback f (Scheme.TwoAffineOpenCover.specMap R A), ⊤)) ∧
    Module.finrank A Γ((Scheme.Modules.pullback (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A))).obj
        (SheafOfModules.unit X.ringCatSheaf), ⊤)
      = Module.finrank A Γ(Limits.pullback f (Scheme.TwoAffineOpenCover.specMap R A), ⊤) := by sorry
