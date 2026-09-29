-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_relEffCartierDiv_supportedIn_rigidify_iso_of_subsingleton_H1_of_support_subset
-- name    : AlgebraicGeometry.RelPicard.exists_relEffCartierDiv_supportedIn_rigidify_iso_of_subsingleton_H1_of_support_subset
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/89c2c7fd-bb3e-55db-9bf0-e1a3c7691762
-- title:
--   Polarised chart divisor over the H¹-vanishing open locus
-- statement:
--   Fix a commutative ring $R$, a separated morphism $c : C \to \operatorname{Spec} R$, a section $\varepsilon$ of $c$, and an open $U \subseteq C$ whose structure morphism $U \hookrightarrow C \to \operatorname{Spec} R$ is smooth of relative dimension $1$; fix $g, e, \rho$ with $g + e = \rho$, a relative effective Cartier divisor $E$ of degree $\rho$ on $C$ over $\operatorname{Spec} R$ whose support lies in the preimage of $U$, and a divisor $D_\gamma$ of degree $e$ with support likewise in $U$. For a rigidified line bundle $L'$ on $C \times_R T'$ write $\Theta(L') = L'.L \otimes (\mathcal{O}(E_{T'}) \otimes \mathcal{I}_{D_{\gamma,T'}})$, where $\mathcal{O}(E_{T'})$ is the dual of the ideal module of the pullback of $E$ and $\mathcal{I}_{D_{\gamma,T'}}$ is the ideal module of the pullback of $D_\gamma$. Four hypotheses are assumed, for all bases locally of finite type over $\operatorname{Spec} R$: (hsect) a section theorem — for an invertible module $M$ on $C \times_R V$ whose fibrewise two-chart Čech complexes have vanishing $H^1$ and one-dimensional $H^0$, and such that over every algebraically closed point every nonzero map from the unit module to the pullback of $M$ has zero-scheme ideal equal to that of a degree-$g$ divisor supported in $U$, there are a degree-$g$ divisor $D_0$ over $V$ and an invertible $N$ on $V$ with $D_0$'s line bundle isomorphic to $M \otimes \mathrm{pr}_2^* N$, and $D_0.I$ is determined by this property among divisors supported in $U$ of arbitrary degree; (hZfib$_\gamma$) for $L'$ satisfying `FibrewiseAlgEquivZero`, every nonzero section of $\Theta(L')$ over a geometric point whose zero-scheme support lies in the preimage of $U$ is cut out by a degree-$g$ divisor supported in $U$; (hH0one) for such $L'$, vanishing of the fibrewise Čech $H^1$ of $\Theta(L')$ forces $\dim_k H^0 = 1$; (havoid) for such $L'$, if all nonzero sections of $\Theta(L')$ at geometric points have zero-scheme support in the preimage of $U$, then any degree-$g$ divisor whose line bundle is $\Theta(L') \otimes \mathrm{pr}_2^* N$ with $N$ invertible is supported in $U$. Here `FibrewiseAlgEquivZero` asks that at each algebraically closed point $s$ the restriction of $L'.L$ to the fibre satisfy `IsAlgEquivZero`, i.e. be connected to the trivial bundle by an invertible module on a geometrically integral family of finite type. Now let $t : T \to \operatorname{Spec} R$ be locally of finite type, $L$ a rigidified line bundle on $C \times_R T$ with `FibrewiseAlgEquivZero`, and $W \subseteq T$ open such that: for every field $k$ and every $s : \operatorname{Spec} k \to T$ with set-theoretic image in $W$, the two-chart Čech $H^1$ of the fibre of $\Theta(L)$ vanishes for every two-chart affine open cover of the fibre; and for every algebraically closed $k$, every $x : \operatorname{Spec} k \to W$ and every nonzero map from the unit module to the pullback of $\Theta(L|_W)$, the support of its zero-scheme ideal is contained in the preimage of $U$ under the first projection. Then there exist a relative effective Cartier divisor $D$ of degree $\rho$ and one $D_0$ of degree $g$ on $C \times_R W$ such that $D.I = D_0.I \cdot \mathcal{I}_{D_{\gamma,W}}$, the rigidification along $\varepsilon$ of $\mathcal{O}(D) \otimes \mathcal{I}_{E_W}$ (that is, this module tensored with the pullback along $\mathrm{pr}_2$ of the dual of its restriction along the rigidifying section) is isomorphic to the restriction of $L$ to $W$, and $D_0$ is supported in $U$.
--
--   This is the divisor-producing step in the construction of open charts for the algebraic-equivalence-zero part of the relative Picard functor of a relative curve, in the variant polarised by a fixed divisor $E$ of degree $\rho = g + e$ rather than by a multiple of the marked section: on the locus $W$ where the twisted bundle $L \otimes \mathcal{O}(E) \otimes \mathcal{I}_{D_\gamma}$ has vanishing fibrewise $H^1$ and no section vanishing outside $U$, it represents $L$ as $\mathcal{O}(D_0 + D_\gamma - E)$ with a moving divisor $D_0$ of degree $g$ inside $U$. It is used to produce an open chart mapping by an open immersion into the algebraic-equivalence-zero cut of the relative sub-Picard presheaf.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_relEffCartierDiv_supportedIn_rigidify_iso_of_subsingleton_H1_of_support_subset.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import Definitions.Def_CategoryTheory_OverTotalPresheaf
import Definitions.Def_AlgebraicGeometry_LocalRepresentabilityULift
import Definitions.Def_AlgebraicGeometry_AffineLimit
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivFunctor
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivRestrict
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivTwist2
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicGeometry_ModulesRigidify

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra

theorem AlgebraicGeometry.RelPicard.exists_relEffCartierDiv_supportedIn_rigidify_iso_of_subsingleton_H1_of_support_subset
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (g e ρ : ℕ) (hr : g + e = ρ)

    (E : RelEffCartierDiv c ρ (𝟙 (Spec (CommRingCat.of R)))) (hEU : E.SupportedIn U)
    (Dγ : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R)))) (hDγ : Dγ.SupportedIn U)

    (hsect : ∀ ⦃V : Scheme.{u}⦄ (u : V ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType u] (M : (pullback c u).Modules),
      Scheme.Modules.IsInvertible M →
      (∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ V) (𝒲 : (pullback (pullback.snd c u) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c u s) (fibreModule c u s M)).H1 ∧
          Module.finrank k (𝒲.sectionsOf (fibreAt c u s) (fibreModule c u s M)).H0 = 1) →
      (∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ V)
        (σ : 𝟙_ (pullback c (x ≫ u)).Modules ⟶ (Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj M), σ ≠ 0 →
        ∃ Dx : RelEffCartierDiv c g (x ≫ u), Dx.I = Scheme.Modules.zeroSchemeIdeal σ ∧ Dx.SupportedIn U) →
      ∃ (D₀ : RelEffCartierDiv c g u) (N : V.Modules), Scheme.Modules.IsInvertible N ∧
        Nonempty (D₀.lineBundle ≅ M ⊗ (Scheme.Modules.pullback (pullback.snd c u)).obj N) ∧
        ∀ (d' : ℕ) (D' : RelEffCartierDiv c d' u) (N' : V.Modules), Scheme.Modules.IsInvertible N' → D'.SupportedIn U →
          Nonempty (D'.lineBundle ≅ M ⊗ (Scheme.Modules.pullback (pullback.snd c u)).obj N') → D'.I = D₀.I)

    (hZfibγ : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
      (L : RigidifiedLineBundle c ε t), FibrewiseAlgEquivZero L →
      ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ T)
        (σ : 𝟙_ (pullback c (x ≫ t)).Modules ⟶ (Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj
          (L.L ⊗ ((E.pullbackAlong t (Category.comp_id t)).lineBundle ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule))), σ ≠ 0 →

        ((Scheme.Modules.zeroSchemeIdeal σ).support : Set ↥(pullback c (x ≫ t))) ⊆ ((pullback.fst c (x ≫ t)) ⁻¹ᵁ U : Set ↥(pullback c (x ≫ t))) →
        ∃ Dx : RelEffCartierDiv c g (x ≫ t), Dx.I = Scheme.Modules.zeroSchemeIdeal σ ∧ Dx.SupportedIn U)

    (hH0one : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) (L : RigidifiedLineBundle c ε t), FibrewiseAlgEquivZero L →
      ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T) (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          (L.L ⊗ ((E.pullbackAlong t (Category.comp_id t)).lineBundle ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)))).H1 →
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          (L.L ⊗ ((E.pullbackAlong t (Category.comp_id t)).lineBundle ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)))).H0 = 1)

    (havoid : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
      (L : RigidifiedLineBundle c ε t), FibrewiseAlgEquivZero L →

      (∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ T)
        (σ : 𝟙_ (pullback c (x ≫ t)).Modules ⟶ (Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj
          (L.L ⊗ ((E.pullbackAlong t (Category.comp_id t)).lineBundle ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule))),
        σ ≠ 0 → ((Scheme.Modules.zeroSchemeIdeal σ).support : Set ↥(pullback c (x ≫ t))) ⊆ ((pullback.fst c (x ≫ t)) ⁻¹ᵁ U : Set ↥(pullback c (x ≫ t)))) →
      ∀ (D₀ : RelEffCartierDiv c g t) (N : T.Modules), Scheme.Modules.IsInvertible N →
        Nonempty (D₀.lineBundle ≅
          (L.L ⊗ ((E.pullbackAlong t (Category.comp_id t)).lineBundle ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)) ⊗
            (Scheme.Modules.pullback (pullback.snd c t)).obj N) →
        D₀.SupportedIn U)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (L : RigidifiedLineBundle c ε t) (hL : FibrewiseAlgEquivZero L) (W : T.Opens)
    (hW : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T), Set.range ⇑s ⊆ (W : Set T) →
      ∀ (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          (L.L ⊗ ((E.pullbackAlong t (Category.comp_id t)).lineBundle ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)))).H1)

    (hWfin : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ (W : Scheme.{u}))
      (σ : 𝟙_ (pullback c (x ≫ W.ι ≫ t)).Modules ⟶ (Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj
        ((L.pullbackAlong (⟨W.ι, rfl⟩ : SchemeHomOver (W.ι ≫ t) t)).L ⊗
          ((E.pullbackAlong (W.ι ≫ t) (Category.comp_id _)).lineBundle ⊗ (Dγ.pullbackAlong (W.ι ≫ t) (Category.comp_id _)).idealModule))),
      σ ≠ 0 → ((Scheme.Modules.zeroSchemeIdeal σ).support : Set ↥(pullback c (x ≫ W.ι ≫ t))) ⊆
        ((pullback.fst c (x ≫ W.ι ≫ t)) ⁻¹ᵁ U : Set ↥(pullback c (x ≫ W.ι ≫ t)))) :
    ∃ (D : RelEffCartierDiv c ρ (W.ι ≫ t)) (D₀ : RelEffCartierDiv c g (W.ι ≫ t)),
      D.I = D₀.I * (Dγ.pullbackAlong (W.ι ≫ t) (Category.comp_id _)).I ∧
      Nonempty (Scheme.Modules.rigidify (RelPicard.rigSection c (W.ι ≫ t) ε) (pullback.snd c (W.ι ≫ t))
          (D.lineBundle ⊗ (E.pullbackAlong (W.ι ≫ t) (Category.comp_id _)).idealModule) ≅
        (L.pullbackAlong (⟨W.ι, rfl⟩ : SchemeHomOver (W.ι ≫ t) t)).L) ∧
      D₀.SupportedIn U := by sorry
