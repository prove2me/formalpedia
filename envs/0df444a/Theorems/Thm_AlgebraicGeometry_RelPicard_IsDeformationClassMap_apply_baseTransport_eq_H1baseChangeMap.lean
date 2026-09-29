-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_IsDeformationClassMap_apply_baseTransport_eq_H1baseChangeMap
-- name    : AlgebraicGeometry.RelPicard.IsDeformationClassMap.apply_baseTransport_eq_H1baseChangeMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/6464eb4d-b0b8-57be-a35a-e40a676cd042
-- title:
--   Base-change compatibility of the deformation class map
-- statement:
--   Let $R$ be a commutative ring, $C$ a scheme, $c\colon C\to\operatorname{Spec}R$ a morphism, and $\varepsilon$ an element of `SchemeHomOver (𝟙 (Spec (.of R))) c`, that is, a morphism $\operatorname{Spec}R\to C$ whose composite with $c$ is the identity. Let $K$ be a commutative $R$-algebra and $\mathcal W$ a two-affine open cover of $C$: two affine opens $U_0,U_1$ with $U_0\sqcup U_1=\top$ and $U_0\sqcap U_1$ affine. Let $\delta$ be any map from `RigKerDualNumber c ε K` — the quotient of the carrier type of rigidified line bundles on $C\times_R\operatorname{Spec}K[\varepsilon]$ by the isomorphism relation — to the Čech $H^1$ of the structure sheaf for the cover $\mathcal W$ pulled back to $C\times_R\operatorname{Spec}K$, and let $\delta'$ be any map of the same shape for the base-changed data $(C\times_R\operatorname{Spec}K\to\operatorname{Spec}K,\ \varepsilon_K,\ \mathcal W_K)$, where $\varepsilon_K$ is `sectionBaseChange` of $\varepsilon$ and $\mathcal W_K=\mathcal W$ pulled back along $\operatorname{pr}_1$. Assume both are deformation class maps, i.e. for a carrier $M$, sections $e_0,e_1$ of $M$'s module over the two opens of the cover pulled back to $C\times_R\operatorname{Spec}K[\varepsilon]$ and $f$ in the degree-$(0,1)$ term of the two-chart complex over $C\times_R\operatorname{Spec}K$, if $e_0$ and $e_1$ are frames on their respective opens and the restriction of $e_1$ to the intersection equals $(1+\varepsilon\cdot f)$ times the restriction of $e_0$, then the value on the class of $M$ is the Čech class of $f$; similarly for $\delta'$. Then for every $m$ in `RigKerDualNumber c ε K`, $\delta'$ applied to the image of $m$ under the transport equivalence `RigKerDualNumber.baseTransport` equals `H1baseChangeMap` — the map on Čech $H^1$ semilinear along $\operatorname{algebraMap} K K$ induced by the cover morphism with underlying scheme map $\operatorname{pr}_1$ — applied to $\delta(m)$.
--
--   This is the compatibility under base change $R\to K$ of the Kodaira–Spencer-type identification of dual-number deformations of rigidified line bundles with classes in $\check H^1(\mathcal O)$ computed on a two-chart cover, stated for arbitrary maps satisfying the deformation class specification rather than for a single constructed map. It is used in the comparison of Čech classes with germs of trace maps for the relative Picard functor, where deformations over $C$ and over its base change to $K$ must be matched.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_IsDeformationClassMap_apply_baseTransport_eq_H1baseChangeMap.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_PicDualNumberDeformationClassSpec
import Definitions.Def_AlgebraicGeometry_RigKerDualNumberBaseTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
  AlgebraicGeometry.SmoothProperCurve NeronModelInfra

namespace AlgebraicGeometry.RelPicard

theorem IsDeformationClassMap.apply_baseTransport_eq_H1baseChangeMap
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R)) (ε : SchemeHomOver (𝟙 (Spec (.of R))) c)
    (K : Type u) [CommRing K] [Algebra R K] (𝒲 : C.TwoAffineOpenCover)
    {δ : RigKerDualNumber c ε K → H1StructureSheaf c K 𝒲}
    {δ' : RigKerDualNumber (baseChange R c K) (sectionBaseChange K ε) K →
      H1StructureSheaf (baseChange R c K) K (𝒲.pullback c K)}
    (hδ : IsDeformationClassMap c ε K 𝒲 δ)
    (hδ' : IsDeformationClassMap (baseChange R c K) (sectionBaseChange K ε) K (𝒲.pullback c K) δ')
    (m : RigKerDualNumber c ε K) :
    δ' (RigKerDualNumber.baseTransport K c ε K m) =
      Scheme.TwoAffineOpenCover.H1baseChangeMap (𝒲.pullback c K) (baseChange R c K) K (δ m) := by sorry
