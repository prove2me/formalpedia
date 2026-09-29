-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_IsAlgEquivZero_nonempty_pullback_iso_pullback_unit_and_eulerChar_eq_one_of_curveModel_ratFunc
-- name    : AlgebraicGeometry.RelPicard.IsAlgEquivZero.nonempty_pullback_iso_pullback_unit_and_eulerChar_eq_one_of_curveModel_ratFunc
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/ff3e542b-0d9f-5d46-a9b3-b0c4934d640a
-- title:
--   Algebraically trivial bundles pulled back to a rational curve model
-- statement:
--   Let $k$ be an algebraically closed field, $X$ a scheme with a structure morphism $x \colon X \to \operatorname{Spec} k$, and $L$ an $\mathcal{O}_X$-module that is invertible, i.e. every point of $X$ has an open neighbourhood $U$ on which the restriction of $L$ is isomorphic to the unit module of $U$. Assume $L$ satisfies `IsAlgEquivZero x L`: there are a scheme $T'$ with a locally of finite type, geometrically integral morphism $h \colon T' \to \operatorname{Spec} k$, an invertible module $M$ on $X \times_{\operatorname{Spec} k} T'$ and two sections $t_0, t_1$ of $h$ over $\operatorname{Spec} k$ such that the pullback of $M$ along the base change of $t_0$ is isomorphic to the unit module, while the pullback along the base change of $t_1$ is isomorphic to the pullback of $L$. Let further $M$ be a `CurveModel k (RatFunc k)`, i.e. an integral scheme $M.C$ with a proper, smooth of relative dimension $1$ morphism $M.\mathrm{toBase} \colon M.C \to \operatorname{Spec} k$, together with a ring isomorphism of its function field with $k(t)$ compatible with $k$, a bijection between the closed points of $M.C$ and the places of $k(t)$ over $k$ matching stalks with valuation subrings, and the property that every finite set of points lies in an affine open. Let $i \colon M.C \to X$ be a morphism with $i$ followed by $x$ equal to $M.\mathrm{toBase}$, let $\mathcal{W}_0$ be a two-affine open cover of $M.C$ (two affine opens $U_0, U_1$ with $U_0 \sqcup U_1 = \top$ and $U_0 \sqcap U_1$ affine), and assume that for every two-affine open cover $\mathcal{W}$ of $M.C$ the two-term Čech complex $\Gamma(\mathcal{O}, U_0) \times \Gamma(\mathcal{O}, U_1) \to \Gamma(\mathcal{O}, U_0 \sqcap U_1)$ of the structure sheaf has $\dim_k H^1 = 0$ and $\dim_k H^0 = 1$. Then the pullback $i^* L$ is isomorphic to $i^*$ of the unit module of $X$, and for every two-affine open cover $\mathcal{W}'$ of $M.C$ the Euler characteristic of the corresponding Čech complex of $i^* L$, namely $\dim_k H^0 - \dim_k H^1$, equals $1$.
--
--   This is the statement that a line bundle algebraically equivalent to zero restricts trivially, with Euler characteristic $1$, to a rational component of a degenerate fibre: the genus-zero hypothesis is supplied in the Čech form $\dim_k H^1(\mathcal{O}) = 0$, $\dim_k H^0(\mathcal{O}) = 1$ for all two-affine covers. It feeds the analysis of the relative Picard functor at Deligne–Rapoport fibres, supplying the vanishing and Euler-characteristic inputs used in the treatment of smooth loci and two-line degenerations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_IsAlgEquivZero_nonempty_pullback_iso_pullback_unit_and_eulerChar_eq_one_of_curveModel_ratFunc.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
open AlgebraicCurve

theorem AlgebraicGeometry.RelPicard.IsAlgEquivZero.nonempty_pullback_iso_pullback_unit_and_eulerChar_eq_one_of_curveModel_ratFunc
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) (h0 : IsAlgEquivZero x L)
    (M : CurveModel k (RatFunc k)) (i : M.C ⟶ X) (hi : i ≫ x = M.toBase)
    (𝒲₀ : M.C.TwoAffineOpenCover)
    (h10 : ∀ 𝒲 : M.C.TwoAffineOpenCover,
      Module.finrank k (𝒲.sectionsOf M.toBase (SheafOfModules.unit M.C.ringCatSheaf : M.C.Modules)).H1 = 0 ∧
      Module.finrank k (𝒲.sectionsOf M.toBase (SheafOfModules.unit M.C.ringCatSheaf : M.C.Modules)).H0 = 1) :
    Nonempty ((Scheme.Modules.pullback i).obj L ≅ (Scheme.Modules.pullback i).obj (SheafOfModules.unit X.ringCatSheaf)) ∧
    ∀ 𝒲' : M.C.TwoAffineOpenCover,
      (Module.finrank k ↥(𝒲'.sectionsOf M.toBase ((Scheme.Modules.pullback i).obj L)).H0 : ℤ) -
        Module.finrank k (𝒲'.sectionsOf M.toBase ((Scheme.Modules.pullback i).obj L)).H1 = 1 := by sorry
