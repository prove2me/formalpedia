-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_cechFinrank_eq_zero_of_forall_comp_mem_kernelPts_of_not_nonempty_pullback_iso_unit
-- name    : AlgebraicGeometry.Polarisation.cechFinrank_eq_zero_of_forall_comp_mem_kernelPts_of_not_nonempty_pullback_iso_unit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/236507ed-5b55-568a-97ca-093447969de1
-- title:
--   Vanishing Čech ranks for L stabilised by a subscheme
-- statement:
--   Let $k$ be an algebraically closed field, and let $f : A \to \operatorname{Spec} k$ carry a relative group law $L$ (functorial multiplication, unit and inverse on $T$-points over $k$, associative, unital, with inverses, and natural in $T$) together with the bundle of properties `AbelianSchemePropertyBundle`, i.e. $f$ is smooth, proper, has connected fibres and admits a relative group law. Let $fY : Y \to \operatorname{Spec} k$ satisfy the same bundle of properties with group law $LY$, and let $j : Y \to A$ be a closed immersion with $j$ followed by $f$ equal to $fY$, which is a homomorphism in the sense that for every $k$-scheme $t : T \to \operatorname{Spec} k$ and all $P, Q \in \operatorname{Hom}_k(T, Y)$ the composite of $LY.\mathrm{mul}\,t\,P\,Q$ with $j$ equals $L.\mathrm{mul}$ applied to $P$ followed by $j$ and $Q$ followed by $j$. Let $\mathcal{L}$ be an $\mathcal{O}_A$-module which is invertible (each point of $A$ has an open neighbourhood $U$ on which the pullback of $\mathcal{L}$ along $U \hookrightarrow A$ is isomorphic to the unit module), assume every $k$-point $y$ of $Y$ composed with $j$ lies in $\mathrm{kernelPts}\,f\,L\,\mathcal{L}$, that is satisfies `L.IsInStabilizer` for $\mathcal{L}$ over the identity of $\operatorname{Spec} k$, and assume the pullback of $\mathcal{L}$ along $j$ is not isomorphic to the unit module on $Y$. Then for every finite linearly ordered cover $\mathcal{K}$ of $A$ by affine opens and every $n \in \mathbb{N}$, the $n$-th Čech rank $\mathrm{cechFinrank}$ of the presheaf of sections of $\mathcal{L}$ over $k$ vanishes: it is the $k$-dimension of $H^0$ for $n = 0$ and of the $(n-1)$-st quotient $\ker d_{n}/\operatorname{im} d_{n-1}$ otherwise.
--
--   This is the cohomological core of Mumford's Riemann–Roch argument on abelian varieties: if a line bundle is stabilised by a positive-dimensional abelian subvariety on which it restricts non-trivially, all its cohomology vanishes, so $\chi(\mathcal{L}) = 0$. It feeds the contrapositive step showing that non-vanishing of the Euler characteristic forces the stabiliser $K(\mathcal{L})$ to be finite, used in the construction of a closed immersion with finite stabiliser scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_cechFinrank_eq_zero_of_forall_comp_mem_kernelPts_of_not_nonempty_pullback_iso_unit.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.cechFinrank_eq_zero_of_forall_comp_mem_kernelPts_of_not_nonempty_pullback_iso_unit
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hA : AbelianSchemePropertyBundle k f)
    {Y : Scheme.{0}} (fY : Y ⟶ Spec (CommRingCat.of k)) (j : Y ⟶ A) [IsClosedImmersion j] (hjf : j ≫ f = fY)
    (LY : RelativeGroupLaw k fY) (hY : AbelianSchemePropertyBundle k fY)
    (hj : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t fY),
      (LY.mul t P Q).1 ≫ j =
        (L.mul t ⟨P.1 ≫ j, by rw [Category.assoc, hjf, P.2]⟩ ⟨Q.1 ≫ j, by rw [Category.assoc, hjf, Q.2]⟩).1)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (hstab : ∀ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) fY,
      (⟨y.1 ≫ j, by rw [Category.assoc, hjf, y.2]⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) ∈ kernelPts f L 𝓛)
    (hne : ¬ Nonempty ((Scheme.Modules.pullback j).obj 𝓛 ≅ 𝟙_ Y.Modules))
    (𝒦 : A.OrderedAffineCover) (n : ℕ) :
    (OModulePresheaf.ofModules f 𝓛).cechFinrank 𝒦 n = 0 := by sorry
