-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_existsUnique_comp_eq_of_isAffineHom_of_invariants
-- name    : AlgebraicGeometry.Scheme.existsUnique_comp_eq_of_isAffineHom_of_invariants
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/83fbf9b0-cb72-5250-a75a-1f734a981bc3
-- title:
--   Invariant presentations of finite quotients are categorical quotients
-- statement:
--   Let $M$ and $X$ be schemes and $\pi : M \to X$ a morphism of schemes, let $H$ be a finite group and $\rho : H \to \operatorname{Aut} M$ a group homomorphism into the automorphism group of $M$ in the category of schemes. Assume: (i) for every $h \in H$, the underlying morphism of $\rho(h)$ followed by $\pi$ equals $\pi$; (ii) $\pi$ is an affine morphism; (iii) the map on underlying topological spaces induced by $\pi$ is surjective; (iv) for every open $V \subseteq X$ the comorphism $\mathcal O_X(V) \to \mathcal O_M(\pi^{-1}V)$ is injective; (v) for every open $V \subseteq X$ the image of that comorphism is exactly the set of sections $s \in \mathcal O_M(\pi^{-1}V)$ fixed by all the maps induced by $\rho(h)$ on $\mathcal O_M(\pi^{-1}V)$ (using that $\rho(h)^{-1}(\pi^{-1}V) = \pi^{-1}V$, which follows from (i)); and (vi) every affine open $U \subseteq M$ with $\rho(h)^{-1}(U) = U$ for all $h$ is of the form $\pi^{-1}V$ for some affine open $V \subseteq X$. Then for every scheme $T$ and every morphism $f : M \to T$ such that $\rho(h)$ followed by $f$ equals $f$ for all $h \in H$, there is a unique morphism $f' : X \to T$ with $\pi$ followed by $f'$ equal to $f$.
--
--   This is the statement that a presentation of $X$ as the quotient of $M$ by the finite group $H$, given sheaf-theoretically by the invariance and affineness conditions (i)–(vi), makes $X$ a categorical quotient: $\pi$ is universal among $H$-invariant morphisms out of $M$. It is used in the construction of a coarse moduli scheme from a quotient of a fine moduli scheme in the Čerednik–Drinfel'd part of the development, where the quotient is produced abstractly and only its invariance properties are known.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_existsUnique_comp_eq_of_isAffineHom_of_invariants.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.existsUnique_comp_eq_of_isAffineHom_of_invariants
    {M X : Scheme.{u}} (π : M ⟶ X) {H : Type v} [Group H] [Finite H] (ρ : H →* Aut M)
    (hπ : ∀ h : H, (ρ h).hom ≫ π = π) (haff : IsAffineHom π) (hsurj : Function.Surjective π.base)
    (hsec : ∀ V : X.Opens, Function.Injective (π.app V))
    (hinv : ∀ V : X.Opens, Set.range (π.app V) =
      {s | ∀ h : H, (ρ h).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hπ h]) s = s})
    (hopen : ∀ U : M.Opens, IsAffineOpen U → (∀ h : H, (ρ h).hom ⁻¹ᵁ U = U) → ∃ V : X.Opens, IsAffineOpen V ∧ π ⁻¹ᵁ V = U) :
    ∀ (T : Scheme.{u}) (f : M ⟶ T), (∀ h : H, (ρ h).hom ≫ f = f) → ∃! f' : X ⟶ T, π ≫ f' = f := by sorry
