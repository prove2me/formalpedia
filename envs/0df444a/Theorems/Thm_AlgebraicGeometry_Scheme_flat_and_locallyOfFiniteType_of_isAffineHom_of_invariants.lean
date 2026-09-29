-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_flat_and_locallyOfFiniteType_of_isAffineHom_of_invariants
-- name    : AlgebraicGeometry.Scheme.flat_and_locallyOfFiniteType_of_isAffineHom_of_invariants
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/5a305466-19e6-5cb9-a452-dd18184a0d0b
-- title:
--   Flatness and finite type for an affine invariant quotient
-- statement:
--   Let $B_0$ be a Dedekind domain and let $M$, $X$ be schemes equipped with morphisms $\pi_M : M \to \operatorname{Spec} B_0$ and $\pi_X : X \to \operatorname{Spec} B_0$, together with a morphism $\pi : M \to X$ over the base, i.e. $\pi$ followed by $\pi_X$ equals $\pi_M$. Let $H$ be a finite group and $\rho : H \to \operatorname{Aut}(M)$ a group homomorphism into the automorphism group of the scheme $M$, such that each $\rho(h)$ commutes with $\pi_M$ (it is an automorphism over $B_0$) and with $\pi$ (so $\pi$ is $H$-invariant). Assume further that $\pi$ is an affine morphism; that for every open $V \subseteq X$ the map on sections $\mathcal{O}_X(V) \to \mathcal{O}_M(\pi^{-1}V)$ induced by $\pi$ is injective; and that its image is exactly the set of sections of $\mathcal{O}_M$ over $\pi^{-1}V$ fixed by all the maps induced by the automorphisms $\rho(h)$ on $\mathcal{O}_M(\pi^{-1}V)$ (this makes sense because $\rho(h)^{-1}(\pi^{-1}V) = \pi^{-1}V$, by $H$-invariance of $\pi$), i.e. $\mathcal{O}_X(V) \cong \mathcal{O}_M(\pi^{-1}V)^H$. If $\pi_M$ is flat and locally of finite type, then so is $\pi_X$: the conclusion asserts both properties for $\pi_X$.
--
--   This is the descent step for a quotient of a scheme by a finite group presented as an affine morphism whose structure sheaf is the sheaf of invariants: over a Dedekind base, flatness and local finiteness of type pass from $M$ to the quotient $X$, using E. Noether's finiteness theorem for invariants of a finite group and the equivalence of flatness with torsion-freeness over a Dedekind domain. It is applied in the construction of the Čerednik–Drinfel'd quotient of a fine moduli scheme of quaternionic type.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_flat_and_locallyOfFiniteType_of_isAffineHom_of_invariants.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.flat_and_locallyOfFiniteType_of_isAffineHom_of_invariants
    {B₀ : Type} [CommRing B₀] [IsDedekindDomain B₀]
    {M X : Scheme.{0}} (πM : M ⟶ Spec (CommRingCat.of B₀)) (πX : X ⟶ Spec (CommRingCat.of B₀))
    (π : M ⟶ X) (hπX : π ≫ πX = πM)
    {H : Type} [Group H] [Finite H] (ρ : H →* Aut M) (hover : ∀ h : H, (ρ h).hom ≫ πM = πM)
    (hπ : ∀ h : H, (ρ h).hom ≫ π = π) (haff : IsAffineHom π)
    (hsec : ∀ V : X.Opens, Function.Injective (π.app V))
    (hinv : ∀ V : X.Opens, Set.range (π.app V) =
      {s | ∀ h : H, (ρ h).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hπ h]) s = s})
    (hflat : Flat πM) (hlft : LocallyOfFiniteType πM) :
    Flat πX ∧ LocallyOfFiniteType πX := by sorry
