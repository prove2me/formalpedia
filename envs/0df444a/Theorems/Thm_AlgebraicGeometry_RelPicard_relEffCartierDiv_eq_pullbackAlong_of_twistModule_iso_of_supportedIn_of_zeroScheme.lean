-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_relEffCartierDiv_eq_pullbackAlong_of_twistModule_iso_of_supportedIn_of_zeroScheme
-- name    : AlgebraicGeometry.RelPicard.relEffCartierDiv_eq_pullbackAlong_of_twistModule_iso_of_supportedIn_of_zeroScheme
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/cbf9af37-864d-5608-934c-6c89987b2424
-- title:
--   Uniqueness half of the check H¹-vanishing divisor chart
-- statement:
--   Let $R$ be a Noetherian commutative ring, $c\colon C\to\operatorname{Spec}R$ a proper morphism, $\varepsilon$ a section of $c$, and $U\subseteq C$ an open subscheme whose structure morphism to $\operatorname{Spec}R$ is smooth of relative dimension $1$ and whose underlying set contains the image of $\varepsilon$. Fix naturals with $g+e=r$ and a relative effective Cartier divisor $D_\gamma$ of degree $e$ for $c$ over $\operatorname{Spec}R$ itself (an ideal sheaf datum on $C$ whose closed subscheme is finite, flat and locally of finite presentation over the base with all fibre ranks $e$), whose support lies in the preimage of $U$. Three hypotheses are assumed. `hsect`: for every $u\colon V\to\operatorname{Spec}R$ locally of finite type and every invertible module $M$ on $C\times_R V$ such that (a) for every field $k$, every $s\colon\operatorname{Spec}k\to V$ and every two-affine open cover of the fibre, the two-chart Čech complex of the restriction of $M$ has vanishing $H^1$ and $H^0$ of $k$-dimension one, and (b) for every algebraically closed $k$, every $x\colon\operatorname{Spec}k\to V$ and every nonzero morphism $\sigma$ from the unit module to the pullback of $M$ to the fibre product over $x$, the zero-scheme ideal of $\sigma$ is the ideal of a degree-$g$ relative effective Cartier divisor supported in $U$; there exist a degree-$g$ divisor $D_0$ over $u$ and an invertible module $N$ on $V$ with $I_{D_0}^{-1}\cong M\otimes\mathrm{pr}_2^*N$, and moreover every divisor $D'$ of any degree over $u$ which is supported in $U$ and satisfies $I_{D'}^{-1}\cong M\otimes\mathrm{pr}_2^*N'$ for some invertible $N'$ has $I_{D'}=I_{D_0}$. `hZfibγ`: condition (b) holds for the module $M_\gamma(L)=L\otimes\bigl(I_\varepsilon^{-r}\otimes I_{D_\gamma,T}\bigr)$, for every $t\colon T\to\operatorname{Spec}R$ locally of finite type and every rigidified line bundle $L$ on $C\times_R T$ (an invertible module trivialised along the section $\varepsilon_T$) satisfying `FibrewiseAlgEquivZero`, i.e. algebraically equivalent to zero on every fibre over an algebraically closed point of $T$, in the sense that its fibre restriction is linked to the trivial bundle by an invertible module on a family over a geometrically integral base. `hH0one`: for every $t$ and every such $L$, vanishing of the two-chart Čech $H^1$ of $M_\gamma(L)$ at a field-valued point of $T$ forces its $H^0$ to have dimension one. Now let $t\colon T\to\operatorname{Spec}R$ be locally of finite type, $L$ a rigidified line bundle with `FibrewiseAlgEquivZero`, and $W\subseteq T$ an open subscheme containing the image of every field-valued point $s$ of $T$ at which the Čech $H^1$ of $M_\gamma(L)$ vanishes for all two-affine open covers. Let $D$ of degree $r$ and $D_0$ of degree $g$ be relative effective Cartier divisors over $W\hookrightarrow T$ with $I_D=I_{D_0}\cdot I_{D_\gamma,W}$, with $D_0$ supported in $U$, and with the rigidified twist of $I_D^{-1}\otimes I_\varepsilon^{r}$ isomorphic to the restriction of $L$ to $W$. Let $t'\colon T'\to\operatorname{Spec}R$ be locally of finite type, $\psi\colon T'\to T$ a morphism over $\operatorname{Spec}R$, and $D'$ of degree $r$, $D_0'$ of degree $g$ over $t'$ with $I_{D'}=I_{D_0'}\cdot I_{D_\gamma,T'}$, $D_0'$ supported in $U$, and the rigidified twist of $I_{D'}^{-1}\otimes I_\varepsilon^{r}$ isomorphic to $\psi^*L$; assume finally that the Čech $H^1$ of $M_\gamma(\psi^*L)$ is trivial for every field-valued point of $T'$ and every two-affine open cover. The conclusion is that the image of $\psi$ is contained in $W$, and that for every $\varphi\colon T'\to W$ whose composite with $W\hookrightarrow T$ is $\psi$ one has $D'=\varphi^*D$.
--
--   This is the uniqueness half of the construction of the charts $J^\gamma$ used to represent the relative Picard functor by effective divisors of degree $g$: the locus where the fibrewise Čech $H^1$ of the twisted bundle vanishes is shown to be universal, and the divisor $D$ over it is compatible with base change. It feeds the chart-existence statement `exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_fibrewise_zeroScheme`, which produces an open immersion into the algebraic-equivalence-zero cut of the relative Picard presheaf.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_relEffCartierDiv_eq_pullbackAlong_of_twistModule_iso_of_supportedIn_of_zeroScheme.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivTwist2
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra
open AlgebraicGeometry.RelPicard

theorem AlgebraicGeometry.RelPicard.relEffCartierDiv_eq_pullbackAlong_of_twistModule_iso_of_supportedIn_of_zeroScheme
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)] (hεU : Set.range ε.1 ⊆ (U : Set C))
    (g e r : ℕ) (hr : g + e = r) (Dγ : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R)))) (hDγ : Dγ.SupportedIn U)
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
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule))), σ ≠ 0 →
        ∃ Dx : RelEffCartierDiv c g (x ≫ t), Dx.I = Scheme.Modules.zeroSchemeIdeal σ ∧ Dx.SupportedIn U)
    (hH0one : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) (L : RigidifiedLineBundle c ε t), FibrewiseAlgEquivZero L →
      ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T) (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)))).H1 →
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)))).H0 = 1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (L : RigidifiedLineBundle c ε t) (hL : FibrewiseAlgEquivZero L) (W : T.Opens)
    (hWmax : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T),
      (∀ (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)))).H1) → Set.range ⇑s ⊆ (W : Set T))
    (D : RelEffCartierDiv c r (W.ι ≫ t)) (D₀ : RelEffCartierDiv c g (W.ι ≫ t))
    (hD : D.I = D₀.I * (Dγ.pullbackAlong (W.ι ≫ t) (Category.comp_id _)).I) (hD₀U : D₀.SupportedIn U)
    (hDL : Nonempty (D.twistModule c ε ≅ (L.pullbackAlong (⟨W.ι, rfl⟩ : SchemeHomOver (W.ι ≫ t) t)).L))
    {T' : Scheme.{u}} (t' : T' ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t'] (ψ : SchemeHomOver t' t)
    (D' : RelEffCartierDiv c r t') (D₀' : RelEffCartierDiv c g t')
    (hD' : D'.I = D₀'.I * (Dγ.pullbackAlong t' (Category.comp_id _)).I) (hD₀'U : D₀'.SupportedIn U)
    (hD'L : Nonempty (D'.twistModule c ε ≅ (L.pullbackAlong ψ).L))
    (h1' : ∀ (k : Type u) [Field k] (s' : Spec (CommRingCat.of k) ⟶ T')
      (𝒲 : (pullback (pullback.snd c t') s').TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t' s') (fibreModule c t' s'
          ((L.pullbackAlong ψ).L ⊗ (sectionTwist c ε t' r ⊗ (Dγ.pullbackAlong t' (Category.comp_id t')).idealModule)))).H1) :
    Set.range ⇑ψ.1 ⊆ (W : Set T) ∧
      ∀ (φ : T' ⟶ W) (hφ : φ ≫ W.ι = ψ.1),
        D' = D.pullbackAlong φ (by rw [← Category.assoc, hφ]; exact ψ.2) := by sorry
