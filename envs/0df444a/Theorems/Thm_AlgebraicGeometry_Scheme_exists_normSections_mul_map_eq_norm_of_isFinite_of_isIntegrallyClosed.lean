-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_normSections_mul_map_eq_norm_of_isFinite_of_isIntegrallyClosed
-- name    : AlgebraicGeometry.Scheme.exists_normSections_mul_map_eq_norm_of_isFinite_of_isIntegrallyClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/d94f0e07-65f6-532e-978f-231ed1cd46f6
-- title:
--   Norm maps along finite surjections onto normal integral schemes
-- statement:
--   There exists an operation $\mathrm{Nf}$ which, for all schemes $X,Y$, every morphism $\pi : X \to Y$ and every open $W \subseteq Y$, sends a section of $\mathcal{O}_X$ over $\pi^{-1}W$ to a section of $\mathcal{O}_Y$ over $W$, and which has the following four properties whenever $\pi : X \to Y$ is finite and surjective, $X$ and $Y$ are integral, and every affine open $U \subseteq Y$ has integrally closed coordinate ring $\Gamma(Y,U)$. First, for each open $W$ the map $\mathrm{Nf}_\pi(W;-)$ sends $1$ to $1$ and satisfies $\mathrm{Nf}_\pi(W;ab) = \mathrm{Nf}_\pi(W;a)\,\mathrm{Nf}_\pi(W;b)$. Second, for opens $W' \le W$ and $a \in \Gamma(X,\pi^{-1}W)$, the norm of the restriction of $a$ to $\pi^{-1}W'$ is the restriction to $W'$ of $\mathrm{Nf}_\pi(W;a)$. Third, for $W$ affine open, with $\Gamma(X,\pi^{-1}W)$ viewed as a $\Gamma(Y,W)$-algebra via $\pi^\sharp$ on $W$, and assuming this algebra is free and finite as a module, $\mathrm{Nf}_\pi(W;a)$ is the algebra norm $\mathrm{Algebra.norm}$, i.e. the determinant of multiplication by $a$. Fourth, given a cartesian square with $g' : X' \to X$, $\pi' : X' \to Y'$, $g : Y' \to Y$ exhibiting $X'$ as the pullback, with $g$ flat, $X'$ and $Y'$ integral and all affine opens of $Y'$ having integrally closed coordinate rings, the norm along $\pi'$ over $g^{-1}W$ of the image of $a$ under $g'^\sharp$, transported along the identification $\pi'^{-1}(g^{-1}W) = g'^{-1}(\pi^{-1}W)$ coming from commutativity of the square, equals the image of $\mathrm{Nf}_\pi(W;a)$ under $g^\sharp$ on $W$.
--
--   This packages the classical norm map $\pi_*\mathcal{O}_X \to \mathcal{O}_Y$ attached to a finite surjective morphism onto a normal integral scheme: multiplicative, compatible with restriction, computed as a determinant on affine opens where the structure sheaf is free, and compatible with flat base change. It is used in the construction of the norm of an invertible module along such a morphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_exists_normSections_mul_map_eq_norm_of_isFinite_of_isIntegrallyClosed.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.exists_normSections_mul_map_eq_norm_of_isFinite_of_isIntegrallyClosed :
    ∃ Nf : ∀ ⦃X Y : Scheme.{u}⦄ (π : X ⟶ Y) (W : Y.Opens), Γ(X, π ⁻¹ᵁ W) → Γ(Y, W),
      ∀ ⦃X Y : Scheme.{u}⦄ (π : X ⟶ Y) [IsFinite π] [Surjective π] [IsIntegral X] [IsIntegral Y],
        (∀ U : Y.Opens, IsAffineOpen U → IsIntegrallyClosed Γ(Y, U)) →

        (∀ W : Y.Opens, Nf π W 1 = 1 ∧ ∀ a b : Γ(X, π ⁻¹ᵁ W), Nf π W (a * b) = Nf π W a * Nf π W b) ∧

        (∀ (W W' : Y.Opens) (h : W' ≤ W) (a : Γ(X, π ⁻¹ᵁ W)),
          Nf π W' (X.presheaf.map (homOfLE (Scheme.Hom.preimage_mono π h)).op a) =
            Y.presheaf.map (homOfLE h).op (Nf π W a)) ∧

        (∀ (W : Y.Opens), IsAffineOpen W →
          letI : Algebra Γ(Y, W) Γ(X, π ⁻¹ᵁ W) := (π.app W).hom.toAlgebra
          ∀ [Module.Free Γ(Y, W) Γ(X, π ⁻¹ᵁ W)] [Module.Finite Γ(Y, W) Γ(X, π ⁻¹ᵁ W)],
          ∀ a : Γ(X, π ⁻¹ᵁ W), Nf π W a = Algebra.norm Γ(Y, W) a) ∧

        (∀ ⦃X' Y' : Scheme.{u}⦄ (g : Y' ⟶ Y) (π' : X' ⟶ Y') (g' : X' ⟶ X) (sq : IsPullback g' π' π g),
          ∀ [Flat g] [IsIntegral X'] [IsIntegral Y'],
          (∀ U : Y'.Opens, IsAffineOpen U → IsIntegrallyClosed Γ(Y', U)) →
          ∀ (W : Y.Opens) (a : Γ(X, π ⁻¹ᵁ W)),
            Nf π' (g ⁻¹ᵁ W) (X'.presheaf.map (eqToHom (show π' ⁻¹ᵁ (g ⁻¹ᵁ W) = g' ⁻¹ᵁ (π ⁻¹ᵁ W) by
                rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, sq.w])).op
              ((g'.app (π ⁻¹ᵁ W)).hom a)) =
            (g.app W).hom (Nf π W a)) := by sorry
