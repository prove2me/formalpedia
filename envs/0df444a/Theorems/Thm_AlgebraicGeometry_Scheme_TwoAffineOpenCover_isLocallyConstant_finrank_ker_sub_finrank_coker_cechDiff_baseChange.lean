-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_isLocallyConstant_finrank_ker_sub_finrank_coker_cechDiff_baseChange
-- name    : AlgebraicGeometry.Scheme.TwoAffineOpenCover.isLocallyConstant_finrank_ker_sub_finrank_coker_cechDiff_baseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/69a595e7-9c5d-53bf-ba37-a7a0171d5495
-- title:
--   Local constancy of the fibrewise Euler characteristic of an invertible module
-- statement:
--   Let $A$ be a Noetherian commutative ring, let $C$ be a scheme and $c \colon C \to \operatorname{Spec} A$ a morphism that is proper and flat, let $\mathcal V$ be a two-chart affine open cover of $C$, i.e. a pair of opens $U_0, U_1 \subseteq C$ with $U_0$, $U_1$ and $U_0 \cap U_1$ affine and $U_0 \cup U_1 = C$, and let $M$ be a sheaf of modules on $C$ which is invertible in the sense that every point of $C$ has an open neighbourhood $U$ such that the pullback of $M$ along the inclusion $U \hookrightarrow C$ is isomorphic to the unit sheaf of modules on $U$. Associated with these data is the two-chart Čech datum $\mathcal V.\mathtt{sectionsOf}\, c\, M$, consisting of the section modules $\Gamma(M, U_0)$, $\Gamma(M, U_1)$, $\Gamma(M, U_0 \cap U_1)$ with their $A$-module structures induced by $c$ and the two restriction maps $r_0, r_1$ to $\Gamma(M, U_0 \cap U_1)$, and its Čech differential $d = (-r_0) \sqcup r_1 \colon \Gamma(M, U_0) \times \Gamma(M, U_1) \to \Gamma(M, U_0 \cap U_1)$, $(s_0,s_1) \mapsto r_1 s_1 - r_0 s_0$, an $A$-linear map. The assertion is that the function on $\operatorname{Spec} A$ sending a prime $\mathfrak p$ to
--   $$\dim_{\kappa(\mathfrak p)} \ker\bigl(d \otimes_A \kappa(\mathfrak p)\bigr) - \dim_{\kappa(\mathfrak p)} \bigl( (\kappa(\mathfrak p) \otimes_A \Gamma(M, U_0 \cap U_1)) / \operatorname{im}(d \otimes_A \kappa(\mathfrak p)) \bigr) \in \mathbb Z,$$
--   where $\kappa(\mathfrak p)$ is the residue field of $\mathfrak p$ and $d \otimes_A \kappa(\mathfrak p)$ is the base change of $d$, is locally constant.
--
--   For a proper flat family the kernel and cokernel of the base-changed two-chart Čech differential compute $\check H^0$ and $\check H^1$ of the fibre, so the displayed integer is the Euler characteristic of the invertible module restricted to the fibre over $\mathfrak p$; the statement is the local constancy of this Euler characteristic in the base. It is used in the construction and analysis of the relative Picard functor, in particular by the results producing a clopen locus where the fibrewise Euler characteristic takes a prescribed value and those controlling $\dim \check H^1$ of the unit bundle on fibres.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_isLocallyConstant_finrank_ker_sub_finrank_coker_cechDiff_baseChange.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.isLocallyConstant_finrank_ker_sub_finrank_coker_cechDiff_baseChange
    {A : Type u} [CommRing A] [IsNoetherianRing A] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of A))
    [IsProper c] [Flat c] (𝒱 : C.TwoAffineOpenCover) (M : C.Modules) (hM : Scheme.Modules.IsInvertible M) :
    IsLocallyConstant fun 𝔭 : PrimeSpectrum A =>
      (Module.finrank 𝔭.asIdeal.ResidueField
          (LinearMap.ker ((𝒱.sectionsOf c M).cechDiff.baseChange 𝔭.asIdeal.ResidueField)) : ℤ) -
        Module.finrank 𝔭.asIdeal.ResidueField
          ((𝔭.asIdeal.ResidueField ⊗[A] (𝒱.sectionsOf c M).M01) ⧸
            LinearMap.range ((𝒱.sectionsOf c M).cechDiff.baseChange 𝔭.asIdeal.ResidueField)) := by sorry
