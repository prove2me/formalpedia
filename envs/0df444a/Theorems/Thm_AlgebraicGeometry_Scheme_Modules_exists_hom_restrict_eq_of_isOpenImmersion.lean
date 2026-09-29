-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_hom_restrict_eq_of_isOpenImmersion
-- name    : AlgebraicGeometry.Scheme.Modules.exists_hom_restrict_eq_of_isOpenImmersion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/ce9aac22-88a1-5317-9ff1-6488b5726bf4
-- title:
--   Gluing a morphism of 𝒪_X-modules along two open immersions
-- statement:
--   Let $X$, $Y_0$, $Y_1$, $Y_{01}$ be schemes, let $f_0 \colon Y_0 \to X$ and $f_1 \colon Y_1 \to X$ be open immersions, and let $g_0 \colon Y_{01} \to Y_0$, $g_1 \colon Y_{01} \to Y_1$ be open immersions such that $g_0$ followed by $f_0$ equals $g_1$ followed by $f_1$. Assume the open ranges of $f_0$ and $f_1$ have supremum $\top$, i.e. the two images cover $X$, and that their intersection is contained in the open range of $g_0 \circ f_0$, so that $Y_{01}$ dominates the overlap. Let $M, N$ be $\mathcal{O}_X$-modules, i.e. objects of `X.Modules`, and let $\psi_0 \colon M|_{Y_0} \to N|_{Y_0}$ and $\psi_1 \colon M|_{Y_1} \to N|_{Y_1}$ be morphisms of the restricted modules, restriction being `Scheme.Modules.restrict`. Assume $\psi_0$ and $\psi_1$ agree after further restriction along $g_0$, resp. $g_1$, to $Y_{01}$, the comparison being made with the canonical isomorphisms `Scheme.Modules.restrictFunctorComp` identifying the iterated restriction with the restriction along the composite, and `Scheme.Modules.restrictFunctorCongr` transporting along the equality $g_0 \circ f_0 = g_1 \circ f_1$. Then there exists a morphism $\varphi \colon M \to N$ of $\mathcal{O}_X$-modules whose restrictions along $f_0$ and along $f_1$, computed by `Scheme.Modules.restrictFunctor`, are exactly $\psi_0$ and $\psi_1$. No uniqueness of $\varphi$ is asserted.
--
--   This is the gluing principle for morphisms of sheaves of modules, in the form adapted to a two-element cover by open immersions together with a scheme dominating the overlap, the typical instances being two opens $U_0, U_1$ covering $X$ with $Y_{01} = U_0 \cap U_1$, or two affine opens with an affine refinement of their intersection. It is used to produce isomorphisms of $\mathcal{O}_X$-modules from compatible linear equivalences on the members of a two-chart affine open cover, as in [`AlgebraicGeometry.Scheme.TwoAffineOpenCover.nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible`](thm.html#AlgebraicGeometry.Scheme.TwoAffineOpenCover.nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_hom_restrict_eq_of_isOpenImmersion.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.exists_hom_restrict_eq_of_isOpenImmersion
    {X Y₀ Y₁ Y₀₁ : Scheme.{u}} (f₀ : Y₀ ⟶ X) (f₁ : Y₁ ⟶ X) [IsOpenImmersion f₀] [IsOpenImmersion f₁]
    (g₀ : Y₀₁ ⟶ Y₀) (g₁ : Y₀₁ ⟶ Y₁) [IsOpenImmersion g₀] [IsOpenImmersion g₁]
    (hg : g₀ ≫ f₀ = g₁ ≫ f₁) (hcov : f₀.opensRange ⊔ f₁.opensRange = ⊤)
    (hov : f₀.opensRange ⊓ f₁.opensRange ≤ (g₀ ≫ f₀).opensRange)
    {M N : X.Modules} (ψ₀ : M.restrict f₀ ⟶ N.restrict f₀) (ψ₁ : M.restrict f₁ ⟶ N.restrict f₁)
    (hψ : (Scheme.Modules.restrictFunctorComp g₀ f₀).hom.app M ≫ (Scheme.Modules.restrictFunctor g₀).map ψ₀ ≫
            (Scheme.Modules.restrictFunctorComp g₀ f₀).inv.app N =
          (Scheme.Modules.restrictFunctorCongr hg).hom.app M ≫
            (Scheme.Modules.restrictFunctorComp g₁ f₁).hom.app M ≫ (Scheme.Modules.restrictFunctor g₁).map ψ₁ ≫
            (Scheme.Modules.restrictFunctorComp g₁ f₁).inv.app N ≫ (Scheme.Modules.restrictFunctorCongr hg).inv.app N) :
    ∃ φ : M ⟶ N, (Scheme.Modules.restrictFunctor f₀).map φ = ψ₀ ∧ (Scheme.Modules.restrictFunctor f₁).map φ = ψ₁ := by sorry
