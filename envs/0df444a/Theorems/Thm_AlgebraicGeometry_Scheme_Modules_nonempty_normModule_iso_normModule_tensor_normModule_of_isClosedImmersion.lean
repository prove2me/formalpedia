-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_normModule_iso_normModule_tensor_normModule_of_isClosedImmersion
-- name    : AlgebraicGeometry.Scheme.Modules.nonempty_normModule_iso_normModule_tensor_normModule_of_isClosedImmersion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/88205385-6eac-5f53-80b2-682b872ca8c5
-- title:
--   Norm of a line bundle splits along a scheme-theoretic union
-- statement:
--   Let $X$ be an integral scheme and let $\pi : Z \to X$, $\iota_0 : Z_0 \to Z$, $\iota_1 : Z_1 \to Z$ be morphisms of schemes with $\iota_0$ and $\iota_1$ closed immersions, and with each of $\pi$, $\iota_0 \,$ followed by $\pi$, and $\iota_1$ followed by $\pi$ finite, flat and locally of finite presentation. Let $d, d_0, d_1$ be natural numbers such that at every point $x$ of $X$ the local rank of $\pi$ equals $d$, that of $\iota_0$ followed by $\pi$ equals $d_0$, that of $\iota_1$ followed by $\pi$ equals $d_1$, and $d = d_0 + d_1$. Assume further that $Z$ is covered by $Z_0$ and $Z_1$ in the sense that for every open $U \subseteq Z$ a section $s \in \Gamma(Z, U)$ whose images under the maps on sections induced by $\iota_0$ and by $\iota_1$ both vanish is itself $0$. Let $L$ be a module on $Z$ which is invertible in the sense that every point of $Z$ has an open neighbourhood $U$ on which the pullback of $L$ along the inclusion of $U$ is isomorphic to the unit module of $U$. Then the type of isomorphisms, in the category of modules on $X$, between $\det^{d}(\pi_* L) \otimes \det^{d}(\pi_* \mathcal{O}_Z)^{\vee}$ and the tensor product of $\det^{d_0}((\iota_0\pi)_* \iota_0^* L) \otimes \det^{d_0}((\iota_0\pi)_* \mathcal{O}_{Z_0})^{\vee}$ with $\det^{d_1}((\iota_1\pi)_* \iota_1^* L) \otimes \det^{d_1}((\iota_1\pi)_* \mathcal{O}_{Z_1})^{\vee}$ is nonempty, where the dual is the internal hom into the unit module.
--
--   This is the multiplicativity of the norm of a line bundle along a finite locally free morphism with respect to a scheme-theoretic decomposition of the source into two closed subschemes of complementary ranks. It feeds the comparison of norm maps on the relative Picard functor used in the study of models of modular curves, being cited in the analysis of the base change of the norm homomorphism and its relation to restriction and Frobenius on points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_nonempty_normModule_iso_normModule_tensor_normModule_of_isClosedImmersion.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.nonempty_normModule_iso_normModule_tensor_normModule_of_isClosedImmersion
    {X Z Z₀ Z₁ : Scheme.{u}} [IsIntegral X] (π : Z ⟶ X) (ι₀ : Z₀ ⟶ Z) (ι₁ : Z₁ ⟶ Z)
    [IsClosedImmersion ι₀] [IsClosedImmersion ι₁]
    [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
    [IsFinite (ι₀ ≫ π)] [Flat (ι₀ ≫ π)] [LocallyOfFinitePresentation (ι₀ ≫ π)]
    [IsFinite (ι₁ ≫ π)] [Flat (ι₁ ≫ π)] [LocallyOfFinitePresentation (ι₁ ≫ π)]
    (d d₀ d₁ : ℕ) (hd : ∀ x : X, π.finrank x = d) (hd₀ : ∀ x : X, (ι₀ ≫ π).finrank x = d₀)
    (hd₁ : ∀ x : X, (ι₁ ≫ π).finrank x = d₁) (hsum : d = d₀ + d₁)
    (hcov : ∀ (U : Z.Opens) (s : Γ(Z, U)), (ι₀.app U).hom s = 0 → (ι₁.app U).hom s = 0 → s = 0)
    {L : Z.Modules} (hL : Scheme.Modules.IsInvertible L) :
    Nonempty (Scheme.Modules.normModule π d L ≅
      Scheme.Modules.normModule (ι₀ ≫ π) d₀ ((Scheme.Modules.pullback ι₀).obj L) ⊗
        Scheme.Modules.normModule (ι₁ ≫ π) d₁ ((Scheme.Modules.pullback ι₁).obj L)) := by sorry
