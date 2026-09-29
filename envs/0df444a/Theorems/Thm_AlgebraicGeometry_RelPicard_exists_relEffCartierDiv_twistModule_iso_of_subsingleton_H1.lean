-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_relEffCartierDiv_twistModule_iso_of_subsingleton_H1
-- name    : AlgebraicGeometry.RelPicard.exists_relEffCartierDiv_twistModule_iso_of_subsingleton_H1
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/f5d9f77a-9f9f-5b15-b61b-e10d3559420a
-- title:
--   Divisor chart where fibrewise H¹ of L(rε-D_γ) vanishes
-- statement:
--   Let $R$ be a Noetherian commutative ring and let $c : C \to \operatorname{Spec} R$ be proper, smooth of relative dimension one and geometrically integral, with $\varepsilon$ a morphism $\operatorname{Spec} R \to C$ satisfying $\varepsilon \cdot c = \mathrm{id}$. Assume the data `h𝔉`: for every $m_0$ there is a `SmoothProperCurve.FiniteMapData` for $c$ and $\varepsilon$ (two affine charts $U, V$ covering $C$ with $U$ the complement of the image of $\varepsilon$, mutually inverse functions $f \in \Gamma(C,U)$, $g \in \Gamma(C,V)$ cutting out $U \cap V$, each finite over a polynomial algebra, whose level sets are free of rank $m$) whose $m$ is at least $m_0$. Fix naturals $g, e, r$ with $g + e = r$ and a relative effective Cartier divisor $D_\gamma$ of degree $e$ on $C$ over the identity base (a finite, flat, finitely presented ideal sheaf on $C \times_R \operatorname{Spec} R$ of fibre rank $e$), normalised by `hχ`: for every algebraically closed field $k$, every $k$-point $x$ of $\operatorname{Spec} R$ and every two-affine open cover of the corresponding fibre, the two-chart Čech Euler characteristic $\dim_k H^0 - \dim_k H^1$ of the fibre module of `sectionTwist c ε (𝟙 _) r ⊗ Dγ.idealModule`, i.e. of $\mathcal O(r\varepsilon - D_\gamma)$, equals $1$. Let $t : T \to \operatorname{Spec} R$ be locally of finite type and let $L$ be a rigidified line bundle on $C \times_R T$ (an invertible module `L.L` with a trivialisation of its restriction along the section `rigSection c t ε`) satisfying `FibrewiseAlgEquivZero`: over every algebraically closed field point of $T$ its restriction to the fibre is algebraically equivalent to zero in the sense of `IsAlgEquivZero`. Let $U \subseteq T$ be an open subset such that for every field $k$ and every morphism $s : \operatorname{Spec} k \to T$ with set-theoretic image contained in $U$, and for every two-affine open cover of the fibre, the Čech $H^1$ of the fibre module of $L \otimes (\mathcal O(r\varepsilon) \otimes \mathcal O(-D_{\gamma}))$, where $D_\gamma$ is pulled back along $t$, is a subsingleton. Then there are relative effective Cartier divisors $D$ of degree $r$ and $D_0$ of degree $g$ on $C$ over $U$ (base morphism $U \hookrightarrow T \to \operatorname{Spec} R$) whose ideals satisfy $I_D = I_{D_0} \cdot I_{D_\gamma|_U}$, together with an isomorphism of modules between `D.twistModule c ε`, the rigidification along `rigSection` of $\mathcal O(D) \otimes (\mathcal I_\varepsilon^{\,r})$, and the restriction of $L$ to $C \times_R U$.
--
--   This is the existence half of the classical description of the charts of the relative Picard functor of a smooth proper curve with a section: on the open locus where $H^1(L(r\varepsilon - D_\gamma))$ vanishes, every line bundle algebraically equivalent to zero is of the form $\mathcal O(D - r\varepsilon)$ for a relative effective divisor $D \ge D_\gamma$ of degree $r$ (Milne, Jacobian Varieties, §4). It feeds the construction of open charts of the algebraic-equivalence-zero part of the relative Picard presheaf, being cited by `exists_openChart_relSubPicPresheaf_algEquivZeroCut_of_relEffCartierDiv`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_relEffCartierDiv_twistModule_iso_of_subsingleton_H1.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivTwist2
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra AlgebraicGeometry.SmoothProperCurve
open AlgebraicGeometry.RelPicard

theorem AlgebraicGeometry.RelPicard.exists_relEffCartierDiv_twistModule_iso_of_subsingleton_H1
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    (g e r : ℕ) (hr : g + e = r) (Dγ : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R))))
    (hχ : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover),
      (Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ Dγ.idealModule))).H0 : ℤ) -
        Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ Dγ.idealModule))).H1 = 1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (L : RigidifiedLineBundle c ε t) (hL : FibrewiseAlgEquivZero L) (U : T.Opens)
    (hU : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T), Set.range ⇑s ⊆ (U : Set T) →
      ∀ (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)))).H1) :
    ∃ (D : RelEffCartierDiv c r (U.ι ≫ t)) (D₀ : RelEffCartierDiv c g (U.ι ≫ t)),
      D.I = D₀.I * (Dγ.pullbackAlong (U.ι ≫ t) (Category.comp_id _)).I ∧
      Nonempty (D.twistModule c ε ≅ (L.pullbackAlong (⟨U.ι, rfl⟩ : SchemeHomOver (U.ι ≫ t) t)).L) := by sorry
