-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward
-- name    : AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_basicOpen_refinement_basis_pushforward
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/55a295e7-e83e-5e6b-9a2d-bbfcf00b7983
-- title:
--   Basic-open refinement of a two-affine cover trivialising π_*mathcal O_Y
-- statement:
--   Let $X$ and $Y$ be schemes and $\pi\colon Y\to X$ a finite, flat morphism that is locally of finite presentation, let $d$ be a natural number, and suppose that the fibre rank `π.finrank x` equals $d$ at every point $x$ of $X$. Assume $X$ is integral and that every closed subset $Z\subseteq X$ with $Z\neq X$ is finite. Let $\mathcal V$ be a `TwoAffineOpenCover` of $X$, that is, a pair of affine opens $U_0,U_1$ with $U_0\sqcup U_1=\top$ and $U_0\cap U_1$ affine, and assume $U_0$ and $U_1$ are non-empty as subsets of $X$. Then there exist sections $f_0\in\Gamma(X,U_0)$, $f_1\in\Gamma(X,U_1)$ and a further `TwoAffineOpenCover` $\mathcal V'$ of $X$ whose two charts are exactly the basic opens $X_{f_0}$ and $X_{f_1}$, such that for each $i\in\{0,1\}$ the $\mathcal O_X$-module obtained by pushing the monoidal unit of the modules over $Y$ (that is, $\mathcal O_Y$) forward along $\pi$ admits sections $e_1,\dots,e_d$ over $\mathcal V'.U_i$ with the property that for every open $W\leq \mathcal V'.U_i$ the restrictions of the $e_j$ to $W$ form a basis of $\Gamma(\pi_*\mathcal O_Y,W)$ as a $\Gamma(X,W)$-module, indexed by `Fin d`.
--
--   This is the refinement step which arranges that, on a curve-like integral base, a cover by two affine charts may be shrunk to basic opens — still affine, with affine intersection, and still covering $X$ — over which the direct image of the structure sheaf along a finite flat morphism of constant rank $d$ is free of rank $d$ compatibly with all further restrictions. It supplies the chartwise bases used by the relative-Picard and norm constructions for $\pi_*L$, and is cited in the construction of deformation-class maps and in the comparison of norm modules over dual numbers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_basicOpen_refinement_basis_pushforward
    {X Y : Scheme.{u}} (π : Y ⟶ X) [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
    (d : ℕ) (hd : ∀ x : X, π.finrank x = d)
    [IsIntegral X]

    (hX : ∀ Z : Set X, IsClosed Z → Z ≠ Set.univ → Z.Finite)
    (𝒱 : X.TwoAffineOpenCover) (h₀ : (𝒱.U0 : Set X).Nonempty) (h₁ : (𝒱.U1 : Set X).Nonempty) :
    ∃ (f₀ : Γ(X, 𝒱.U0)) (f₁ : Γ(X, 𝒱.U1)) (𝒱' : X.TwoAffineOpenCover),
      𝒱'.U0 = X.basicOpen f₀ ∧ 𝒱'.U1 = X.basicOpen f₁ ∧
      (∃ e : Fin d → Γ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules), 𝒱'.U0),
        ∀ (W : X.Opens) (hW : W ≤ 𝒱'.U0),
          ∃ b : Module.Basis (Fin d) Γ(X, W) Γ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules), W),
            ∀ i, b i = ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules)).presheaf.map (homOfLE hW).op (e i)) ∧
      (∃ e : Fin d → Γ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules), 𝒱'.U1),
        ∀ (W : X.Opens) (hW : W ≤ 𝒱'.U1),
          ∃ b : Module.Basis (Fin d) Γ(X, W) Γ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules), W),
            ∀ i, b i = ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules)).presheaf.map (homOfLE hW).op (e i)) := by sorry
