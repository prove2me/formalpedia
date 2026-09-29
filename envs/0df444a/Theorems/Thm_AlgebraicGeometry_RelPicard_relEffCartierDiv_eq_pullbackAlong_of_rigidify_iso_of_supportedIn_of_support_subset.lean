-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_relEffCartierDiv_eq_pullbackAlong_of_rigidify_iso_of_supportedIn_of_support_subset
-- name    : AlgebraicGeometry.RelPicard.relEffCartierDiv_eq_pullbackAlong_of_rigidify_iso_of_supportedIn_of_support_subset
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/6ab6a474-a053-55e6-99a6-2658ea8cdba2
-- title:
--   Factorisation through W and uniqueness of the chart divisor
-- statement:
--   Let $R$ be a Noetherian commutative ring, $c\colon C\to\operatorname{Spec}R$ a proper morphism, $\varepsilon$ a section of $c$, and $U\subseteq C$ an open subscheme whose inclusion followed by $c$ is smooth of relative dimension $1$; let $g+e=\rho$ in $\mathbb{N}$. Fix relative effective Cartier divisors $E$ of degree $\rho$ and $D_\gamma$ of degree $e$ for $c$ over $\mathrm{id}_{\operatorname{Spec}R}$, both with support inside the preimage of $U$ under the first projection. Three global hypotheses are assumed: (`hsect`) for every $u\colon V\to\operatorname{Spec}R$ locally of finite type and every invertible module $M$ on $C\times_R V$ whose fibres have two-chart Čech $H^1$ subsingleton and $H^0$ of $k$-dimension $1$, and all of whose nonzero maps from the unit object over a geometric point have zero scheme (in the sense of `Scheme.Modules.zeroSchemeIdeal`) equal to the ideal of a degree-$g$ relative effective Cartier divisor supported in $U$, there are a degree-$g$ divisor $D_0$ over $u$ and an invertible $N$ on $V$ with $\mathcal{O}(D_0)$, the dual of the ideal module of $D_0$, isomorphic to $M$ tensored with the pullback of $N$, and any divisor $D'$ of any degree over $u$ supported in $U$ whose line bundle is of this shape has the same ideal as $D_0$; (`hZfibγ`) the same zero-scheme conclusion for nonzero $\sigma$ into the pullback of $L.L\otimes(\mathcal{O}(E_t)\otimes I_{D_{\gamma,t}})$, for every rigidified line bundle $L$ over a base $t$ locally of finite type satisfying `FibrewiseAlgEquivZero`, under the extra assumption that the support of the zero scheme lies over $U$; (`hH0one`) for such $L$, vanishing of the two-chart Čech $H^1$ of the fibre of $L.L\otimes(\mathcal{O}(E_t)\otimes I_{D_{\gamma,t}})$ forces $\dim_k H^0=1$. Now let $t\colon T\to\operatorname{Spec}R$ be locally of finite type, $L$ a rigidified line bundle for $c,\varepsilon$ over $t$ with `FibrewiseAlgEquivZero`, and $W\subseteq T$ open and maximal in the sense that every geometric point $s$ of $T$ at which the Čech $H^1$ of the fibre of $L.L\otimes(\mathcal{O}(E_t)\otimes I_{D_{\gamma,t}})$ vanishes for all two-chart affine open covers and at which every nonzero $\sigma$ from the unit object has zero scheme supported over $U$ has image contained in $W$. Over $W$ are given divisors $D$ of degree $\rho$ and $D_0$ of degree $g$ with $D.I=D_0.I\cdot I_{D_{\gamma,W}}$, $D_0$ supported in $U$, and with the rigidification along `rigSection` of $\mathcal{O}(D)\otimes I_{E_W}$ isomorphic to the restriction of $L$ to $W$. Finally let $t'\colon T'\to\operatorname{Spec}R$ be locally of finite type, $\psi\colon T'\to T$ a morphism over $\operatorname{Spec}R$, and $D'$ of degree $\rho$, $D_0'$ of degree $g$ over $t'$ satisfying the same three conditions with respect to the pullback of $L$ along $\psi$, together with vanishing of the Čech $H^1$ of all fibres of $(L|_{\psi}).L\otimes(\mathcal{O}(E_{t'})\otimes I_{D_{\gamma,t'}})$ over all fields, and the condition that over every geometric point of $T'$ each nonzero $\sigma$ into the pullback of that module has zero scheme supported over $U$. The conclusion is that the set-theoretic image of $\psi$ is contained in $W$ and that, for every $\varphi\colon T'\to W$ with $\varphi$ followed by the inclusion of $W$ equal to $\psi$, $D'$ equals the pullback of $D$ along $\varphi$.
--
--   This is the uniqueness and maximality step for the polarised open chart of the relative Picard functor, in the form where the twist is by the fixed divisor $E$ rather than a multiple of the section $\varepsilon$: it says that a test base carrying divisor data of the chart's shape necessarily maps into the maximal chart locus $W$, and that its divisor is then the base change of the chart's divisor. It is used in [`AlgebraicGeometry.RelPicard.exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_polarisation_of_fibrewise_zeroScheme`](thm.html#AlgebraicGeometry.RelPicard.exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_polarisation_of_fibrewise_zeroScheme), which produces an open immersion of such a chart into the subpresheaf of the relative Picard presheaf cut out by fibrewise algebraic equivalence to zero.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_relEffCartierDiv_eq_pullbackAlong_of_rigidify_iso_of_supportedIn_of_support_subset.lean

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

theorem AlgebraicGeometry.RelPicard.relEffCartierDiv_eq_pullbackAlong_of_rigidify_iso_of_supportedIn_of_support_subset
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
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
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (L : RigidifiedLineBundle c ε t) (hL : FibrewiseAlgEquivZero L) (W : T.Opens)

    (hWmax : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T),
      (∀ (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          (L.L ⊗ ((E.pullbackAlong t (Category.comp_id t)).lineBundle ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)))).H1) →
      (∀ (σ : 𝟙_ (pullback c (s ≫ t)).Modules ⟶ (Scheme.Modules.pullback (mapOnProdOver c s rfl)).obj
          (L.L ⊗ ((E.pullbackAlong t (Category.comp_id t)).lineBundle ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule))),
        σ ≠ 0 → ((Scheme.Modules.zeroSchemeIdeal σ).support : Set ↥(pullback c (s ≫ t))) ⊆ ((pullback.fst c (s ≫ t)) ⁻¹ᵁ U : Set ↥(pullback c (s ≫ t)))) →
      Set.range ⇑s ⊆ (W : Set T))
    (D : RelEffCartierDiv c ρ (W.ι ≫ t)) (D₀ : RelEffCartierDiv c g (W.ι ≫ t))
    (hD : D.I = D₀.I * (Dγ.pullbackAlong (W.ι ≫ t) (Category.comp_id _)).I) (hD₀U : D₀.SupportedIn U)
    (hDL : Nonempty (Scheme.Modules.rigidify (RelPicard.rigSection c (W.ι ≫ t) ε) (pullback.snd c (W.ι ≫ t))
        (D.lineBundle ⊗ (E.pullbackAlong (W.ι ≫ t) (Category.comp_id _)).idealModule) ≅
      (L.pullbackAlong (⟨W.ι, rfl⟩ : SchemeHomOver (W.ι ≫ t) t)).L))
    {T' : Scheme.{u}} (t' : T' ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t'] (ψ : SchemeHomOver t' t)
    (D' : RelEffCartierDiv c ρ t') (D₀' : RelEffCartierDiv c g t')
    (hD' : D'.I = D₀'.I * (Dγ.pullbackAlong t' (Category.comp_id _)).I) (hD₀'U : D₀'.SupportedIn U)
    (hD'L : Nonempty (Scheme.Modules.rigidify (RelPicard.rigSection c t' ε) (pullback.snd c t')
        (D'.lineBundle ⊗ (E.pullbackAlong t' (Category.comp_id _)).idealModule) ≅ (L.pullbackAlong ψ).L))
    (h1' : ∀ (k : Type u) [Field k] (s' : Spec (CommRingCat.of k) ⟶ T')
      (𝒲 : (pullback (pullback.snd c t') s').TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t' s') (fibreModule c t' s'
          ((L.pullbackAlong ψ).L ⊗ ((E.pullbackAlong t' (Category.comp_id t')).lineBundle ⊗ (Dγ.pullbackAlong t' (Category.comp_id t')).idealModule)))).H1)

    (hfin' : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ T')
      (σ : 𝟙_ (pullback c (x ≫ t')).Modules ⟶ (Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj
        ((L.pullbackAlong ψ).L ⊗ ((E.pullbackAlong t' (Category.comp_id t')).lineBundle ⊗ (Dγ.pullbackAlong t' (Category.comp_id t')).idealModule))),
      σ ≠ 0 → ((Scheme.Modules.zeroSchemeIdeal σ).support : Set ↥(pullback c (x ≫ t'))) ⊆ ((pullback.fst c (x ≫ t')) ⁻¹ᵁ U : Set ↥(pullback c (x ≫ t')))) :
    Set.range ⇑ψ.1 ⊆ (W : Set T) ∧
      ∀ (φ : T' ⟶ W) (hφ : φ ≫ W.ι = ψ.1),
        D' = D.pullbackAlong φ (by rw [← Category.assoc, hφ]; exact ψ.2) := by sorry
