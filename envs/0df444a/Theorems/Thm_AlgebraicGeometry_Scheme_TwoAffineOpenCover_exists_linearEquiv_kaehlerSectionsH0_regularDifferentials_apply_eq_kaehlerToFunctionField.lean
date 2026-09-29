-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_kaehlerSectionsH0_regularDifferentials_apply_eq_kaehlerToFunctionField
-- name    : AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_linearEquiv_kaehlerSectionsH0_regularDifferentials_apply_eq_kaehlerToFunctionField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/ce33c174-0dc4-557b-9150-6c8974e1650d
-- title:
--   Global Čech 1-forms are the regular differentials of k(X)
-- statement:
--   Let $k$ be a perfect field, $X$ a scheme, and $\mathcal{V}$ a two-chart affine open cover of $X$, i.e. opens $U_0, U_1 \subseteq X$, both affine, with $U_0 \sqcup U_1 = \top$ and $U_0 \sqcap U_1$ affine. Let $c : X \to \operatorname{Spec} k$ be a morphism, with $X$ integral, $c$ proper and smooth of relative dimension $1$, and both $U_0$ and $U_1$ non-empty. Each $\Gamma(X,U)$ is a $k$-algebra through $c$, and the function field $X.\mathrm{functionField}$ is a $k$-algebra through `baseToFunctionField c`, the germ at the generic point of $c$ on global sections. The module $(\mathcal{V}.\mathrm{kaehlerSections}\ c).H0$ is the kernel of $(-r_0) \oplus r_1$ on $\Omega_{\Gamma(X,U_0)/k} \times \Omega_{\Gamma(X,U_1)/k}$, the restriction maps $r_i$ to $\Omega_{\Gamma(X,U_0 \sqcap U_1)/k}$ being induced by the restriction ring homomorphisms; thus its elements are pairs of Kähler differentials agreeing on the overlap. The assertion is the existence of a $k$-linear isomorphism $e_\Omega$ from this module onto the submodule $\mathrm{regularDifferentials}\ k\ X.\mathrm{functionField}$ of $\Omega_{k(X)/k}$, consisting of those $\omega$ such that for every place $v$ of $k(X)$ over $k$ (a valuation subring, not all of $k(X)$, containing the image of $k$ and a principal ideal ring) one has $\omega = f \cdot v.\mathrm{dCoord}$ for some $f$ in that valuation subring, with the compatibility that $e_\Omega \omega$ is, as an element of $\Omega_{k(X)/k}$, the image `kaehlerToFunctionField c 𝒱.U0 ω.val.1` of the first component under the generic germ map.
--
--   This is the comparison between the global $1$-forms $H^0(X,\Omega^1_{X/k})$ of a smooth proper curve, computed from a two-chart cover, and the differentials of the function field that are regular at every place; the inclusion of one into the other is `kaehlerToFunctionField_mem_regularDifferentials`, while the content here is that the generic germ is a bijection onto the regular differentials. It underlies the computation of $\dim_k H^0(X,\Omega^1) = g$ over an algebraically closed field, the identification of the chart-level Serre pairing with the residue pairing of the function field, and the description of differentials on modular curves in terms of chart maps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_kaehlerSectionsH0_regularDifferentials_apply_eq_kaehlerToFunctionField.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_KaehlerToFunctionField
import Definitions.Def_AlgebraicCurve_RegularDifferentials

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_linearEquiv_kaehlerSectionsH0_regularDifferentials_apply_eq_kaehlerToFunctionField
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover)
    (c : X ⟶ Spec (CommRingCat.of k))
    [IsIntegral X] [IsProper c] [SmoothOfRelativeDimension 1 c] [Nonempty 𝒱.U0] [Nonempty 𝒱.U1] :
    letI := (baseToFunctionField c).toAlgebra
    ∃ eΩ : ↥((𝒱.kaehlerSections c).H0) ≃ₗ[k] ↥(regularDifferentials k X.functionField),
      ∀ ω : ↥((𝒱.kaehlerSections c).H0),
        (eΩ ω : Ω[X.functionField⁄k]) = kaehlerToFunctionField c 𝒱.U0 ω.val.1 := by sorry
