-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_baseChange_sections_of_isIso_fromTildeGamma
-- name    : AlgebraicGeometry.Scheme.Modules.isIso_baseChange_sections_of_isIso_fromTildeGamma
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/fbadd360-ab01-5bc6-8b54-c1c1d3320a4a
-- title:
--   Affine base change for global sections of 𝒪-modules
-- statement:
--   Let $\varphi\colon R\to S$ be a morphism of commutative rings, write $f=\operatorname{Spec}\varphi\colon\operatorname{Spec}S\to\operatorname{Spec}R$, and let $\mathcal M$ be a sheaf of modules over the structure sheaf of $\operatorname{Spec}R$, i.e. an object `M` of `(Spec R).Modules`. Assume that the canonical comparison morphism `M.fromTildeΓ`, from the sheaf of modules associated with the $R$-module of global sections of $\mathcal M$ to $\mathcal M$ itself, is an isomorphism. Consider the $R$-linear map obtained by applying the global-sections functor `moduleSpecΓFunctor` to the unit $\mathcal M\to f_*f^*\mathcal M$ of the adjunction between `Scheme.Modules.pullback (Spec.map φ)` and pushforward along $f$, followed by the component of the isomorphism `Scheme.Modules.pushforwardSpecCompΓIso φ` at $f^*\mathcal M$, which identifies the global sections of a pushforward $f_*\mathcal N$ with the restriction of scalars along $\varphi$ of the global sections of $\mathcal N$. Transporting this map across the hom-equivalence of the adjunction `ModuleCat.extendRestrictScalarsAdj φ.hom` in the direction from $R$-linear maps $\Gamma(\mathcal M)\to\varphi_*\Gamma(f^*\mathcal M)$ to $S$-linear maps out of $S\otimes_R\Gamma(\mathcal M)$, the assertion is that the resulting $S$-linear map $S\otimes_R\Gamma(\operatorname{Spec}R,\mathcal M)\to\Gamma(\operatorname{Spec}S,f^*\mathcal M)$, $s\otimes m\mapsto s\cdot f^*m$, is an isomorphism.
--
--   This is the affine case of base change for global sections of quasi-coherent modules (degree-zero cohomology and base change), under the hypothesis that $\mathcal M$ is recovered from its global sections. It underlies the statements on sections of base changes and of pullbacks of locally trivial modules, including [`AlgebraicGeometry.Scheme.Modules.exists_linearEquiv_sections_baseChange_of_locallyTrivial`](thm.html#AlgebraicGeometry.Scheme.Modules.exists_linearEquiv_sections_baseChange_of_locallyTrivial), [`AlgebraicGeometry.Scheme.Modules.exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial`](thm.html#AlgebraicGeometry.Scheme.Modules.exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial) and [`AlgebraicGeometry.Scheme.Modules.isIso_baseChangeHom_of_isAffineHom`](thm.html#AlgebraicGeometry.Scheme.Modules.isIso_baseChangeHom_of_isAffineHom).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_isIso_baseChange_sections_of_isIso_fromTildeGamma.lean

import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Definitions.Def_AlgebraicGeometry_ModulesTildePullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.isIso_baseChange_sections_of_isIso_fromTildeGamma
    {R S : CommRingCat.{u}} (φ : R ⟶ S) (M : (Spec R).Modules) (hM : IsIso M.fromTildeΓ) :
    IsIso (((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv
        ((moduleSpecΓFunctor (R := R)).obj M)
        ((moduleSpecΓFunctor (R := S)).obj ((Scheme.Modules.pullback (Spec.map φ)).obj M))).symm
      ((moduleSpecΓFunctor (R := R)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app M) ≫
        (Scheme.Modules.pushforwardSpecCompΓIso φ).hom.app ((Scheme.Modules.pullback (Spec.map φ)).obj M))) := by sorry
