-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_pullback_map_counit_app_ne_zero_of_forall_fibre
-- name    : AlgebraicGeometry.RelPicard.pullback_map_counit_app_ne_zero_of_forall_fibre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/b000885e-5fa7-5f21-969b-cbfe72f99c8b
-- title:
--   Fibrewise non-vanishing of the counit for an invertible module
-- statement:
--   Let $R$ be a Noetherian commutative ring, and let $c : C \to \operatorname{Spec} R$ be proper and smooth of relative dimension $1$, equipped with $\varepsilon$, a morphism $\operatorname{Spec} R \to C$ whose composite with $c$ is the identity. Assume that for every $m_0 \in \mathbb{N}$ there is a datum `SmoothProperCurve.FiniteMapData` for $c$ and $\varepsilon$ — two affine opens $U, V$ with $U \sqcup V = \top$, $U$ the complement of the image of $\varepsilon$, sections $f \in \Gamma(C,U)$, $g \in \Gamma(C,V)$ with $U \sqcap V$ equal to both basic opens and with $f\,g = 1$ there, both finite over the polynomial algebra over $R$, and with level sets over local $R$-algebras finite free of rank $m$ — whose integer $m$ is at least $m_0$. Let $t : T \to \operatorname{Spec} R$ be locally of finite type and $M$ a module on $C \times_{\operatorname{Spec} R} T$ which is invertible, i.e. locally isomorphic to the unit sheaf. Assume that for every field $k$, every $s : \operatorname{Spec} k \to T$ and every two-affine open cover $\mathcal{W}$ of the fibre product $(C\times_{\operatorname{Spec} R} T) \times_T \operatorname{Spec} k$, the two-chart Čech $H^1$ of the sections complex of $\mathcal{W}$ for the restricted structure morphism and the pulled-back module vanishes, while its $H^0$ has $k$-dimension $1$. Then for every field $k$ and every $x : \operatorname{Spec} k \to T$, the pullback along $1_C \times x : C \times_{\operatorname{Spec} R} \operatorname{Spec} k \to C \times_{\operatorname{Spec} R} T$ (formed by `mapOnProdOver`, with $\operatorname{Spec} k$ over $\operatorname{Spec} R$ via $x$ followed by $t$) of the counit at $M$ of the adjunction between pullback and pushforward along the second projection $C \times_{\operatorname{Spec} R} T \to T$ is a nonzero morphism of modules.
--
--   This is the non-vanishing half of cohomology and base change in degree zero for a line bundle on a relative smooth proper curve whose fibres have $h^0 = 1$ and $h^1 = 0$: the evaluation map $q^*q_*M \to M$ restricts to a nonzero map on each fibre. It is used in the construction of a relative effective Cartier divisor together with an isomorphism of line bundles, [`AlgebraicGeometry.RelPicard.exists_relEffCartierDiv_lineBundle_iso_of_forall_fibre`](thm.html#AlgebraicGeometry.RelPicard.exists_relEffCartierDiv_lineBundle_iso_of_forall_fibre), within the relative Picard machinery.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_pullback_map_counit_app_ne_zero_of_forall_fibre.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_ModulesBaseChangeHom
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.RelPicard
open NeronModelInfra MonoidalCategory AlgebraicGeometry.SmoothProperCurve

theorem AlgebraicGeometry.RelPicard.pullback_map_counit_app_ne_zero_of_forall_fibre
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (M : (pullback c t).Modules) (hM : Scheme.Modules.IsInvertible M)
    (hfib : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
      (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1 ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H0 = 1)
    {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ T) :
    (Scheme.Modules.pullback (mapOnProdOver c x rfl)).map
      ((Scheme.Modules.pullbackPushforwardAdjunction (pullback.snd c t)).counit.app M) ≠ 0 := by sorry
