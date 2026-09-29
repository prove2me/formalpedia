-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_tensorProduct_sections_pullback_of_isPullback
-- name    : AlgebraicGeometry.Scheme.Modules.exists_linearEquiv_tensorProduct_sections_pullback_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/78d4eba8-7f5f-5f61-afc2-3071cfcd7505
-- title:
--   Transport of sections base change to any cartesian square
-- statement:
--   Let $R$ be a commutative ring, let $X$ be a scheme with a morphism $f : X \to \operatorname{Spec} R$, and let $M$ be an $\mathcal{O}_X$-module. The hypothesis `hbc` asks that base change of global sections hold for the fibre products chosen by Mathlib: for every $R$-algebra $A$, writing $p_1 =$ `pullback.fst` $f\,(\operatorname{Spec}$ of the structure map $R \to A)$, and giving $\Gamma(M, \top)$ the $R$-module structure obtained by restricting scalars along the ring map $R \to \Gamma(X, \top)$ coming from $f$ (via the inverse of `Scheme.ΓSpecIso` and `f.appLE ⊤ ⊤`), and $\Gamma(p_1^{*}M, p_1^{-1}\top)$ the analogous $A$-module structure coming from the second projection, there is an $A$-linear isomorphism $e : A \otimes_R \Gamma(M, \top) \to \Gamma(p_1^{*}M, p_1^{-1}\top)$ with $e(a \otimes m) = a \cdot (p_1^{*}m)$, where $p_1^{*}m$ denotes `pullbackLocalSection`, the image of $m$ under the unit of the pullback–pushforward adjunction. Given in addition a commutative ring $B$, a ring homomorphism $\varphi : R \to B$, a scheme $X'$ and morphisms $f' : X' \to \operatorname{Spec} B$, $g : X' \to X$ forming a cartesian square `IsPullback g f' f (Spec.map φ)`, the conclusion asserts the same statement for this square: with $\Gamma(M, \top)$ an $R$-module through $f$, with $\Gamma(g^{*}M, g^{-1}\top)$ a $B$-module through $f'$ (via `f'.appLE ⊤ (g ⁻¹ᵁ ⊤) le_top`), and with $B$ an $R$-algebra through $\varphi$, there is a $B$-linear isomorphism $e : B \otimes_R \Gamma(M, \top) \to \Gamma(g^{*}M, g^{-1}\top)$ satisfying $e(b \otimes m) = b \cdot (g^{*}m)$ for all $b \in B$ and $m \in \Gamma(M, \top)$.
--
--   This is the transport step for base change of global sections: it upgrades the statement from the particular fibre product $X \times_{\operatorname{Spec} R} \operatorname{Spec} B$ furnished by the chosen limit to an arbitrary cartesian square over $\operatorname{Spec}\varphi$, keeping the explicit formula $b \otimes m \mapsto b \cdot g^{*}m$ on pullbacks of sections. It is used by the base-change statements for sections of line bundles on fake elliptic curves and in the treatment of good reduction of Jacobians.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_tensorProduct_sections_pullback_of_isPullback.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.Scheme.Modules.exists_linearEquiv_tensorProduct_sections_pullback_of_isPullback
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (M : X.Modules)
    (hbc : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom f M ⊤
      letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
        (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap R A))
        ((Scheme.Modules.pullback (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A))).obj M)
        ((Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A)) ⁻¹ᵁ ⊤)
      ∃ e : A ⊗[R] Γ(M, ⊤) ≃ₗ[A]
          Γ((Scheme.Modules.pullback (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A))).obj M, (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A)) ⁻¹ᵁ ⊤),
        ∀ (a : A) (m : Γ(M, ⊤)),
          e (a ⊗ₜ[R] m) = a • Scheme.Modules.pullbackLocalSection (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A)) m)
    (B : Type u) [CommRing B] (φ : R →+* B)
    (X' : Scheme.{u}) (f' : X' ⟶ Spec (CommRingCat.of B)) (g : X' ⟶ X)
    (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ))) :
    letI : Module R Γ(M, ⊤) := Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop).hom
    letI : Module B Γ((Scheme.Modules.pullback g).obj M, g ⁻¹ᵁ ⊤) :=
      Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ f'.appLE ⊤ (g ⁻¹ᵁ ⊤) le_top).hom
    letI : Algebra R B := φ.toAlgebra
    ∃ e : B ⊗[R] Γ(M, ⊤) ≃ₗ[B] Γ((Scheme.Modules.pullback g).obj M, g ⁻¹ᵁ ⊤),
      ∀ (b : B) (m : Γ(M, ⊤)), e (b ⊗ₜ[R] m) = b • Scheme.Modules.pullbackLocalSection g m := by sorry
