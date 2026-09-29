-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_norm_isInvertible_tensor_pullback_normModule_of_isFinite_of_isIntegrallyClosed
-- name    : AlgebraicGeometry.Scheme.Modules.exists_norm_isInvertible_tensor_pullback_normModule_of_isFinite_of_isIntegrallyClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/2f2bc21e-a138-5a93-9e79-249d9774f491
-- title:
--   Norm of invertible sheaves along a finite surjective map to a normal scheme
-- statement:
--   The assertion is the existence of a rule $\mathrm{Nm}$ which, for all schemes $X,Y$ (in a fixed universe) and every morphism $\pi\colon X\to Y$, sends an $\mathcal{O}_X$-module $L$ (an object of `X.Modules`) to an $\mathcal{O}_Y$-module $\mathrm{Nm}_\pi L$, with the following six properties whenever $\pi$ is finite and surjective, $X$ and $Y$ are integral, and $\Gamma(Y,U)$ is integrally closed for every affine open $U\subseteq Y$. Here `Scheme.Modules.IsInvertible M` means that every point of the base has an open neighbourhood $U$ for which the restriction of $M$ along the inclusion $U\hookrightarrow$ base is isomorphic to the unit sheaf of modules on $U$. (1) If $L$ is invertible then so is $\mathrm{Nm}_\pi L$. (2) If $L$ is invertible and $L\cong L'$ then $\mathrm{Nm}_\pi L\cong\mathrm{Nm}_\pi L'$. (3) For invertible $L,L'$ one has $\mathrm{Nm}_\pi(L\otimes L')\cong \mathrm{Nm}_\pi L\otimes\mathrm{Nm}_\pi L'$. (4) $\mathrm{Nm}_\pi(\mathcal{O}_X)\cong\mathcal{O}_Y$, for the monoidal units. (5) Flat base change: for every pullback square with sides $g'\colon X'\to X$, $\pi'\colon X'\to Y'$, $\pi$, $g\colon Y'\to Y$, with $g$ flat, $X'$ and $Y'$ integral and $\Gamma(Y',U)$ integrally closed for all affine opens $U\subseteq Y'$, and every invertible $L$ on $X$, $g^{*}\mathrm{Nm}_\pi L\cong\mathrm{Nm}_{\pi'}(g'^{*}L)$. (6) Agreement with the determinant norm on the finite locally free locus: for an open $V\subseteq Y$ and $d\in\mathbb{N}$ such that the restriction $\pi\mid_V$ is flat, locally of finite presentation and has fibre rank $d$ at every point of $V$, and every invertible $L$, the restriction of $\mathrm{Nm}_\pi L$ to $V$ is isomorphic to `normModule (π ∣_ V) d` applied to the restriction of $L$ to $\pi^{-1}V$, that is to $\det_d\bigl((\pi\mid_V)_*L\bigr)\otimes \det_d\bigl((\pi\mid_V)_*\mathcal{O}\bigr)^{\vee}$, where the dual is the internal hom into the unit. All isomorphisms are asserted merely as nonempty types, so no naturality or coherence is claimed, and $\mathrm{Nm}$ itself is only a rule on objects, with no functoriality in $L$.
--
--   This is the norm (Weil restriction of a line bundle) along a finite surjective morphism onto a normal integral base, which requires no flatness of $\pi$ and reduces on the finite locally free locus to $\det \pi_*L\otimes(\det\pi_*\mathcal{O}_X)^{-1}$. It is used to construct Hecke correspondences on Deligne–Rapoport models of modular curves, where the relevant covering maps are finite and surjective but not everywhere flat.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_norm_isInvertible_tensor_pullback_normModule_of_isFinite_of_isIntegrallyClosed.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesNormModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Modules.exists_norm_isInvertible_tensor_pullback_normModule_of_isFinite_of_isIntegrallyClosed :
    ∃ Nm : ∀ ⦃X Y : Scheme.{u}⦄, (X ⟶ Y) → X.Modules → Y.Modules,
      ∀ ⦃X Y : Scheme.{u}⦄ (π : X ⟶ Y) [IsFinite π] [Surjective π] [IsIntegral X] [IsIntegral Y],
        (∀ U : Y.Opens, IsAffineOpen U → IsIntegrallyClosed Γ(Y, U)) →

        (∀ L : X.Modules, Scheme.Modules.IsInvertible L → Scheme.Modules.IsInvertible (Nm π L)) ∧

        (∀ L L' : X.Modules, Scheme.Modules.IsInvertible L → Nonempty (L ≅ L') →
          Nonempty (Nm π L ≅ Nm π L')) ∧

        (∀ L L' : X.Modules, Scheme.Modules.IsInvertible L → Scheme.Modules.IsInvertible L' →
          Nonempty (Nm π (L ⊗ L') ≅ Nm π L ⊗ Nm π L')) ∧

        Nonempty (Nm π (𝟙_ X.Modules) ≅ 𝟙_ Y.Modules) ∧

        (∀ ⦃X' Y' : Scheme.{u}⦄ (g : Y' ⟶ Y) (π' : X' ⟶ Y') (g' : X' ⟶ X), IsPullback g' π' π g →
          ∀ [Flat g] [IsIntegral X'] [IsIntegral Y'],
          (∀ U : Y'.Opens, IsAffineOpen U → IsIntegrallyClosed Γ(Y', U)) →
          ∀ L : X.Modules, Scheme.Modules.IsInvertible L →
            Nonempty ((Scheme.Modules.pullback g).obj (Nm π L) ≅
              Nm π' ((Scheme.Modules.pullback g').obj L))) ∧

        (∀ (V : Y.Opens) (d : ℕ), Flat (π ∣_ V) → LocallyOfFinitePresentation (π ∣_ V) →
          (∀ y : V, (π ∣_ V).finrank y = d) →
          ∀ L : X.Modules, Scheme.Modules.IsInvertible L →
            Nonempty ((Scheme.Modules.pullback V.ι).obj (Nm π L) ≅
              Scheme.Modules.normModule (π ∣_ V) d ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj L))) := by sorry
