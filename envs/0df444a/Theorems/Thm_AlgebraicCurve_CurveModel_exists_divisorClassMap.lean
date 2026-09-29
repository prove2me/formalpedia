-- Prove2me | Theorems.Thm_AlgebraicCurve_CurveModel_exists_divisorClassMap
-- name    : AlgebraicCurve.CurveModel.exists_divisorClassMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/24b25f6b-5216-51d2-82fd-cbf972214e5e
-- title:
--   Divisor class map on a smooth proper curve model
-- statement:
--   Let $k$ be an algebraically closed field and $F$ a field extension of $k$ satisfying `IsCurveOver k F` (principal divisors exist, every place has residue field finite over $k$, and $\Omega_{F/k}$ is free of rank one over $F$), and let $M$ be a `CurveModel k F`: an integral scheme $M.C$ with a structure morphism $M.\mathrm{toBase} : M.C \to \operatorname{Spec} k$ that is proper and smooth of relative dimension one, a ring isomorphism of $F$ with the function field of $M.C$ compatible with $k$, a bijection between closed points of $M.C$ and places of $F/k$ matching stalks with valuation subrings, and the property that every finite set of points lies in an affine open. The assertion is that there exists a map $\mathrm{cl}$ from the $\mathcal O_{M.C}$-module objects of $M.C$ to $\mathrm{Pic}(k,F)$, the quotient of the group $\mathrm{Divisor}(k,F)$ of finitely supported $\mathbb Z$-valued functions on places by the subgroup of principal divisors, with the following five properties. First, $\mathrm{cl}$ is an isomorphism invariant on invertible modules: if $L$ is invertible (locally isomorphic to the unit sheaf of modules at each point) and $L \cong L'$, then $\mathrm{cl}(L) = \mathrm{cl}(L')$. Second, $\mathrm{cl}(L \otimes L') = \mathrm{cl}(L) + \mathrm{cl}(L')$ for invertible $L, L'$. Third, $\mathrm{cl}$ of the monoidal unit is $0$. Fourth, for every section $P : \operatorname{Spec} k \to M.C$ of $M.\mathrm{toBase}$ and every $n \in \mathbb N$, writing $v_P$ for the place corresponding to $P$ under `M.pointEquivPlace`, the dual of the module of the ideal sheaf $P.\mathrm{ker}^n$ has class the image of $n\,\delta_{v_P}$, and that module itself has class the image of $-n\,\delta_{v_P}$. Fifth, for every cover $\mathcal V$ of $M.C$ by two affine opens with affine intersection, every invertible $L$, and every divisor $D$ whose class is $\mathrm{cl}(L)$, the two-term Čech complex `𝒱.sectionsOf M.toBase L` has $H^0$ (the kernel of the Čech differential on $\Gamma(L,U_0)\times\Gamma(L,U_1)$) and $H^1$ (the cokernel in $\Gamma(L,U_0\cap U_1)$) finite-dimensional over $k$, with $\dim_k H^0 = \ell(D) = \dim_k L(D)$ and $(\dim_k H^0 - \dim_k H^1) - (\dim_k H^0(\mathcal O) - \dim_k H^1(\mathcal O)) = \deg D$, where the degree is the sum of the coefficients of $D$ weighted by the degrees of the places.
--
--   This packages the classical identification of invertible sheaves on a smooth proper curve with divisor classes of its function field, together with the Riemann–Roch numerics computed through a two-chart Čech complex, as a single map into the divisor class group of the abstract function field $F$. It is used for the computation of $H^0$ of the invertible modules attached to sums of sections, and for the construction of the Abel–Jacobi description of the identity component of the relative Picard group of a curve model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_CurveModel_exists_divisorClassMap.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicCurve

theorem AlgebraicCurve.CurveModel.exists_divisorClassMap
    {k : Type u} [Field k] [IsAlgClosed k] {F : Type v} [Field F] [Algebra k F] [IsCurveOver k F] (M : CurveModel k F) :
    ∃ cl : M.C.Modules → Pic k F,
      (∀ L L' : M.C.Modules, Scheme.Modules.IsInvertible L → Nonempty (L ≅ L') → cl L = cl L') ∧
      (∀ L L' : M.C.Modules, Scheme.Modules.IsInvertible L → Scheme.Modules.IsInvertible L' →
        cl (L ⊗ L') = cl L + cl L') ∧
      cl (𝟙_ M.C.Modules) = 0 ∧
      (∀ (P : {p : Spec (CommRingCat.of k) ⟶ M.C // p ≫ M.toBase = 𝟙 _}) (n : ℕ),
        cl (((P.1.ker) ^ n).invModule) =
            QuotientAddGroup.mk (n • Finsupp.single (M.pointEquivPlace P) (1 : ℤ)) ∧
          cl (((P.1.ker) ^ n).module) =
            QuotientAddGroup.mk (-(n • Finsupp.single (M.pointEquivPlace P) (1 : ℤ)))) ∧
      (∀ (𝒱 : M.C.TwoAffineOpenCover) (L : M.C.Modules), Scheme.Modules.IsInvertible L →
        ∀ D : Divisor k F, QuotientAddGroup.mk D = cl L →
          Module.Finite k (𝒱.sectionsOf M.toBase L).H0 ∧ Module.Finite k (𝒱.sectionsOf M.toBase L).H1 ∧
          Module.finrank k (𝒱.sectionsOf M.toBase L).H0 = ell D ∧
          ((Module.finrank k (𝒱.sectionsOf M.toBase L).H0 : ℤ) - Module.finrank k (𝒱.sectionsOf M.toBase L).H1) -
            ((Module.finrank k (𝒱.sectionsOf M.toBase (𝟙_ M.C.Modules)).H0 : ℤ) -
              Module.finrank k (𝒱.sectionsOf M.toBase (𝟙_ M.C.Modules)).H1) = Divisor.degree D) := by sorry
