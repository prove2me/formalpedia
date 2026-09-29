-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_eulerChar_pullback_tensor_invModule_pow_ker_tensor_module_prod_ker_eq_of_twoLineDegeneration
-- name    : AlgebraicGeometry.RelPicard.eulerChar_pullback_tensor_invModule_pow_ker_tensor_module_prod_ker_eq_of_twoLineDegeneration
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/c8bf52d4-7fce-516f-a73c-1eb9a0223a40
-- title:
--   Euler characteristic g+1 on the section component of a two-line fibre
-- statement:
--   Let $R$ be a commutative ring, $c : C \to \operatorname{Spec} R$ a separated morphism of schemes, $U \subseteq C$ an open subscheme such that the composite of the inclusion $U.\iota$ with $c$ is smooth of relative dimension $1$, and $\varepsilon$ a section of $c$ (a morphism $\operatorname{Spec} R \to C$ with $\varepsilon \circ c = \mathrm{id}$, in the guise of `SchemeHomOver`) whose image lies in $U$. Let $e, r, g$ be natural numbers with $g + e = r$, let $k$ be an algebraically closed field and $s : \operatorname{Spec} k \to \operatorname{Spec} R$. Let $M_1, M_2$ be curve models over $k$ with function field $k(T)$, that is, integral schemes proper and smooth of relative dimension $1$ over $\operatorname{Spec} k$ together with an isomorphism of their function field with `RatFunc k` compatible with $k$ and a bijection `placeEquiv` between their closed points and the places of $k(T)/k$ matching stalks with valuation subrings, and let $i_1 : M_1.C \to C \times_{\operatorname{Spec} R} \operatorname{Spec} k$, $i_2 : M_2.C \to C \times_{\operatorname{Spec} R} \operatorname{Spec} k$ be morphisms, $i_1$ being a morphism over $\operatorname{Spec} k$ (its composite with `pullback.snd` is $M_1.\mathrm{toBase}$). Assume: the images of $i_1$ and $i_2$ on points cover the fibre; there are $n$ and units $a, b : \mathrm{Fin}\, n \to k^\times$ such that every coincidence $i_1(p) = i_2(q)$ has $p$ the closed point of $M_1$ attached to the place of $k(T)$ at $a_i$ and $q$ the closed point of $M_2$ attached to the place at $b_i$ for some $i$; $i_1$ carries the point attached to the place at infinity to the closed point of the base change `sectionFibrePoint ε s` of $\varepsilon$ along $s$; the intersection of the image of $i_1$ with the preimage of $U$ under `pullback.fst` is exactly the connected component of that preimage containing this section point; none of the points $i_1(a_i)$ lies in the preimage of $U$; $W_1$ is an open of the fibre whose underlying set is the complement of the image of $i_2$, the restriction of $i_1$ to the preimage of $W_1$ being an open immersion. Let $v : \mathrm{Fin}\, e \to$ sections of `pullback.snd c s` over $\operatorname{Spec} k$, each with closed-point image in that same connected component, and let $L_0$ be a module on the fibre which is invertible (locally isomorphic to the unit sheaf) and whose pullback along $i_1$ is isomorphic to the pullback along $i_1$ of the unit sheaf. Then for every two-affine open cover $\mathcal{W}'$ of $M_1.C$ (two affine opens with affine intersection covering $M_1.C$), the $k$-ranks of the two-chart Čech cohomology modules of the pullback along $i_1$ of $L_0 \otimes \big(((\ker(\mathrm{sectionFibrePoint}\ \varepsilon\ s))^r)^{\vee} \otimes (\prod_j \ker v_j)\big)$, computed from the sections over the cover relative to $M_1.\mathrm{toBase}$, satisfy $\operatorname{finrank} H^0 - \operatorname{finrank} H^1 = g + 1$ in $\mathbb{Z}$, where $H^0$ is the kernel and $H^1$ the cokernel of the Čech difference map.
--
--   This is the Riemann–Roch computation on the component containing the section in a fibre that degenerates into two rational curves: the twist $L_0(r\varepsilon_s - \sum_j v_j)$ restricted to the $\mathbb{P}^1$ carrying $\varepsilon_s$ has Euler characteristic $1 + r - e = g + 1$, the divisors being supported in the locus where $i_1$ is an open immersion. It feeds the construction of the injection with vanishing $H^1$ on blocks used for two-line degenerations with the section in the smooth locus, `exists_injective_forall_subsingleton_H1_of_blocks_of_twoLineDegeneration_of_sectionInSmoothLocus`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_eulerChar_pullback_tensor_invModule_pow_ker_tensor_module_prod_ker_eq_of_twoLineDegeneration.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000

universe u

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra AlgebraicCurve
open AlgebraicGeometry.RelPicard

theorem AlgebraicGeometry.RelPicard.eulerChar_pullback_tensor_invModule_pow_ker_tensor_module_prod_ker_eq_of_twoLineDegeneration
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (hεU : Set.range ε.1 ⊆ (U : Set C))
    (e r : ℕ) (g : ℕ) (hr : g + e = r)
    (k : Type u) [Field k] [IsAlgClosed k] [DecidableEq (RatFunc k)]
    (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (M₁ M₂ : CurveModel k (RatFunc k)) (i₁ : M₁.C ⟶ pullback c s) (i₂ : M₂.C ⟶ pullback c s)
    (n : ℕ) (a b : Fin n → kˣ)
    (hi₁ : i₁ ≫ pullback.snd c s = M₁.toBase)
    (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    (hinter : ∀ (p : M₁.C) (q : M₂.C), i₁.base p = i₂.base q →
          ∃ i, p = (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 ∧
          q = (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k (b i : k))).1)
    (hεinf : i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeInfty k)).1 = ((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k))
    (hcomp : Set.range i₁.base ∩ ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) =
          connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k)))
    (hnodesU : ∀ i, i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 ∉
          (pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens))
    (W₁ : (pullback c s).Opens) (hW₁eq : (W₁ : Set ↥(pullback c s)) = (Set.range i₂.base)ᶜ)
    [IsOpenImmersion ((i₁ ⁻¹ᵁ W₁).ι ≫ i₁)]

    (v : Fin e → {q : Spec (CommRingCat.of k) ⟶ pullback c s // q ≫ pullback.snd c s = 𝟙 _})
    (hvcomp : ∀ j, ((v j).1).base (IsLocalRing.closedPoint k) ∈
        connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s))
          (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k)))

    (L₀ : (pullback c s).Modules) (hL₀ : Scheme.Modules.IsInvertible L₀)
    (hL₀₁ : Nonempty ((Scheme.Modules.pullback i₁).obj L₀ ≅
        (Scheme.Modules.pullback i₁).obj (SheafOfModules.unit (pullback c s).ringCatSheaf))) :
    ∀ 𝒲' : M₁.C.TwoAffineOpenCover,
      (Module.finrank k ↥(𝒲'.sectionsOf M₁.toBase ((Scheme.Modules.pullback i₁).obj
          (L₀ ⊗ ((((sectionFibrePoint ε s).1.ker) ^ r).invModule ⊗ (∏ j, (v j).1.ker).module)))).H0 : ℤ) -
        Module.finrank k (𝒲'.sectionsOf M₁.toBase ((Scheme.Modules.pullback i₁).obj
          (L₀ ⊗ ((((sectionFibrePoint ε s).1.ker) ^ r).invModule ⊗ (∏ j, (v j).1.ker).module)))).H1 = g + 1 := by sorry
