-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_exists_isInvertible_locIsoOnBase_pullback_of_locIsoOnBase_of_faithfullyFlat_of_section
-- name    : AlgebraicGeometry.Polarisation.exists_isInvertible_locIsoOnBase_pullback_of_locIsoOnBase_of_faithfullyFlat_of_section
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/591ef842-2fb7-5ac5-8f76-ff9453de4b2e
-- title:
--   Faithfully flat descent of invertible modules, up to base-local isomorphism
-- statement:
--   Let $R$ be a commutative ring and $R'$ a commutative $R$-algebra which is faithfully flat as an $R$-module, and let $A, A', A''$ be schemes. Let $f : A \to \operatorname{Spec} R$ be quasi-compact and separated, and assume that for every commutative $R$-algebra $T$ the canonical map from $T$ to $\Gamma(A \times_{\operatorname{Spec} R} \operatorname{Spec} T, \mathcal{O})$ — the $T$-algebra structure being the one induced by the projection to $\operatorname{Spec} T$ — is bijective. Let $e : \operatorname{Spec} R \to A$ satisfy $e$ followed by $f$ equal to the identity. Let $f' : A' \to \operatorname{Spec} R'$ and $g : A' \to A$ form a pullback square over $\operatorname{Spec} R' \to \operatorname{Spec} R$, and let $f'' : A'' \to \operatorname{Spec}(R' \otimes_R R')$ together with $a_1, a_2 : A'' \to A'$ form pullback squares over the two inclusions $R' \to R' \otimes_R R'$ (`includeLeft` and `includeRight`), with $a_1$ followed by $g$ equal to $a_2$ followed by $g$. Let $\mathcal{L}'$ be a module over $A'$ which is invertible, in the sense that every point of $A'$ has an open neighbourhood on which the restriction of $\mathcal{L}'$ is isomorphic to the unit sheaf of modules. Assume $a_1^* \mathcal{L}'$ and $a_2^* \mathcal{L}'$ are isomorphic locally on the base: every point of $\operatorname{Spec}(R' \otimes_R R')$ has an open neighbourhood $U$ with the restrictions of the two pullbacks to $(f'')^{-1}(U)$ isomorphic. The conclusion is that there exists a module $\mathcal{L}$ over $A$, invertible in the same sense, such that $g^* \mathcal{L}$ and $\mathcal{L}'$ are isomorphic locally on the base: every point of $\operatorname{Spec} R'$ has an open neighbourhood $U$ with the restrictions of $g^* \mathcal{L}$ and of $\mathcal{L}'$ to $(f')^{-1}(U)$ isomorphic.
--
--   This is the descent step for invertible modules along a faithfully flat affine base change, in the weakened form in which both the cocycle hypothesis and the conclusion are only isomorphisms locally on the base, the relevant notion for the relative Picard functor of a quasi-compact separated morphism with a section and with $f_*\mathcal{O} = \mathcal{O}$ universally. It is used in the construction of polarisation data on fake elliptic curves in the Čerednik–Drinfel'd setting, both over the base and after localisation at a prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_exists_isInvertible_locIsoOnBase_pullback_of_locIsoOnBase_of_faithfullyFlat_of_section.lean

import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Polarisation
open scoped TensorProduct

universe u

theorem AlgebraicGeometry.Polarisation.exists_isInvertible_locIsoOnBase_pullback_of_locIsoOnBase_of_faithfullyFlat_of_section
    {R : Type u} [CommRing R] (R' : Type u) [CommRing R'] [Algebra R R'] [Module.FaithfullyFlat R R']
    {A A' A'' : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R)) [QuasiCompact f] [IsSeparated f]
    (hH0 : ∀ (T : Type u) [CommRing T] [Algebra R T],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (pullback.snd f (Scheme.TwoAffineOpenCover.specMap R T)) ⊤
      Function.Bijective (algebraMap T Γ(pullback f (Scheme.TwoAffineOpenCover.specMap R T), ⊤)))
    (e : Spec (CommRingCat.of R) ⟶ A) (he : e ≫ f = 𝟙 _)
    (f' : A' ⟶ Spec (CommRingCat.of R')) (g : A' ⟶ A)
    (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
    (f'' : A'' ⟶ Spec (CommRingCat.of (R' ⊗[R] R'))) (a₁ a₂ : A'' ⟶ A')
    (ha₁ : IsPullback a₁ f'' f'
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : R' →ₐ[R] R' ⊗[R] R').toRingHom)))
    (ha₂ : IsPullback a₂ f'' f'
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : R' →ₐ[R] R' ⊗[R] R').toRingHom)))
    (hga : a₁ ≫ g = a₂ ≫ g)
    (𝓛' : A'.Modules) (h𝓛' : Scheme.Modules.IsInvertible 𝓛')
    (hdd : LocIsoOnBase f'' ((Scheme.Modules.pullback a₁).obj 𝓛') ((Scheme.Modules.pullback a₂).obj 𝓛')) :
    ∃ 𝓛 : A.Modules, Scheme.Modules.IsInvertible 𝓛 ∧ LocIsoOnBase f' ((Scheme.Modules.pullback g).obj 𝓛) 𝓛' := by sorry
