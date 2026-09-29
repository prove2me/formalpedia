-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_iff_exists_units_of_sectionsOf_equiv_lineBundle
-- name    : AlgebraicGeometry.Scheme.TwoAffineOpenCover.nonempty_iso_iff_exists_units_of_sectionsOf_equiv_lineBundle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/90e408cb-2b28-5157-a8d5-d0f52ae2eaec
-- title:
--   Two chart-trivial line bundles are isomorphic iff their cocycles agree
-- statement:
--   Let $R$ be a commutative ring, $X$ a scheme, $c : X \to \operatorname{Spec} R$ a morphism, and $\mathcal V$ a `TwoAffineOpenCover` of $X$, that is, a pair of opens $U_0, U_1$ with $U_0$, $U_1$ and $U_0 \sqcap U_1$ affine and $U_0 \sqcup U_1 = \top$. Write $A_0 = \Gamma(X, U_0)$, $A_1 = \Gamma(X, U_1)$, $A_{01} = \Gamma(X, U_0 \sqcap U_1)$ for the rings of `𝒱.cover c`, made $R$-algebras via $c$, with $\rho_0, \rho_1$ the two restriction $R$-algebra maps into $A_{01}$. Let $L, L'$ be objects of `X.Modules` satisfying `Scheme.Modules.IsInvertible`, i.e. each point of $X$ has an open neighbourhood $U$ over which the pullback along $U.\iota$ is isomorphic to the unit sheaf of modules. Let $t, t' \in A_{01}^\times$. Assume given, for $L$, linear equivalences $e_0 : \Gamma(L, U_0) \simeq A_0$ over $A_0$, $e_1 : \Gamma(L, U_1) \simeq A_1$ over $A_1$ and $e_{01} : \Gamma(L, U_0 \sqcap U_1) \simeq A_{01}$ over $A_{01}$ (the modules and restriction maps $r_0, r_1$ of `𝒱.sectionsOf c L`), such that $e_{01}(r_0 x) = \rho_0(e_0 x)$ for all $x$ and $e_{01}(r_1 y) = t \cdot \rho_1(e_1 y)$ for all $y$; and likewise $e_0', e_1', e_{01}'$ for $L'$ with $t'$ in place of $t$. Then the type of isomorphisms $L \cong L'$ is nonempty if and only if there exist units $a_0 \in A_0^\times$ and $a_1 \in A_1^\times$ with $t' = \rho_0(a_0) \cdot t \cdot \rho_1(a_1^{-1})$.
--
--   This is the statement that, for a cover of $X$ by two affine opens with affine intersection, the map from $\check{H}^1(\mathcal V, \mathcal O_X^\times)$ to $\operatorname{Pic} X$ is injective on classes of line bundles presented by a unit on the overlap: two such bundles are isomorphic exactly when their gluing units differ by a coboundary $\rho_0(a_0)\rho_1(a_1)^{-1}$. It is used in the analysis of the relative Picard functor, in the construction of trivial-modulo-deformations classes compatible with tensor products.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_iff_exists_units_of_sectionsOf_equiv_lineBundle.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.nonempty_iso_iff_exists_units_of_sectionsOf_equiv_lineBundle
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    {L L' : X.Modules} (hL : Scheme.Modules.IsInvertible L) (hL' : Scheme.Modules.IsInvertible L')
    (t t' : (𝒱.cover c).A01ˣ)
    (e0 : (𝒱.sectionsOf c L).M0 ≃ₗ[(𝒱.cover c).A0] (𝒱.cover c).A0)
    (e1 : (𝒱.sectionsOf c L).M1 ≃ₗ[(𝒱.cover c).A1] (𝒱.cover c).A1)
    (e01 : (𝒱.sectionsOf c L).M01 ≃ₗ[(𝒱.cover c).A01] (𝒱.cover c).A01)
    (he0 : ∀ x, e01 ((𝒱.sectionsOf c L).r0 x) = (𝒱.cover c).ρ0 (e0 x))
    (he1 : ∀ y, e01 ((𝒱.sectionsOf c L).r1 y) = (t : (𝒱.cover c).A01) * (𝒱.cover c).ρ1 (e1 y))
    (e0' : (𝒱.sectionsOf c L').M0 ≃ₗ[(𝒱.cover c).A0] (𝒱.cover c).A0)
    (e1' : (𝒱.sectionsOf c L').M1 ≃ₗ[(𝒱.cover c).A1] (𝒱.cover c).A1)
    (e01' : (𝒱.sectionsOf c L').M01 ≃ₗ[(𝒱.cover c).A01] (𝒱.cover c).A01)
    (he0' : ∀ x, e01' ((𝒱.sectionsOf c L').r0 x) = (𝒱.cover c).ρ0 (e0' x))
    (he1' : ∀ y, e01' ((𝒱.sectionsOf c L').r1 y) = (t' : (𝒱.cover c).A01) * (𝒱.cover c).ρ1 (e1' y)) :
    Nonempty (L ≅ L') ↔
      ∃ (a0 : (𝒱.cover c).A0ˣ) (a1 : (𝒱.cover c).A1ˣ),
        (t' : (𝒱.cover c).A01) =
          (𝒱.cover c).ρ0 (a0 : (𝒱.cover c).A0) * t * (𝒱.cover c).ρ1 ((a1⁻¹ : (𝒱.cover c).A1ˣ) : (𝒱.cover c).A1) := by sorry
