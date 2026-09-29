-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_openCharts_relSubPicPresheaf_algEquivZeroCut_of_relEffCartierDiv_supportedIn_of_fibrewise_zeroScheme
-- name    : AlgebraicGeometry.RelPicard.exists_openCharts_relSubPicPresheaf_algEquivZeroCut_of_relEffCartierDiv_supportedIn_of_fibrewise_zeroScheme
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/cc3e3dac-841e-5b5c-aa29-9d68606c1ada
-- title:
--   Milne charts for relative Pic⁰ inside the smooth locus
-- statement:
--   Throughout, $R$ is a Noetherian commutative ring, $C$ is a scheme and $c \colon C \to \operatorname{Spec} R$ is proper and flat, $\mathcal V$ is a two-affine open cover of $C$ (two affine opens covering $C$ whose intersection is affine), and $\varepsilon$ is a section of $c$, i.e. a morphism $\operatorname{Spec} R \to C$ with $\varepsilon \circ c$ — in diagrammatic order $\varepsilon.1 \gg c$ — equal to the identity. The functor under consideration is `relSubPicPresheaf c ε (algEquivZeroCut c ε)`: the subfunctor of the relative Picard presheaf on $R$-schemes cut out by the condition `FibrewiseAlgEquivZero`, namely that a rigidified line bundle $L$ on $C \times_R T$ (a line bundle together with a trivialisation of its pullback along the section `rigSection c t ε`) has, for every algebraically closed field $k$ and every $s \colon \operatorname{Spec} k \to T$, the property `IsAlgEquivZero` for the restriction of $L$ to the fibre $C_s$: there are a geometrically integral morphism $T' \to \operatorname{Spec} k$ locally of finite type, an invertible module on $C_s \times_k T'$ and two sections of $T' \to \operatorname{Spec} k$ along which it becomes trivial, respectively isomorphic to the given bundle. Its `overTotal` presheaf on schemes sends $T$ to the pairs consisting of a structure morphism $t \colon T \to \operatorname{Spec} R$ and a class in this cut of the relative Picard set over $t$.
--
--   The numerical data are natural numbers $g, e, r$ with $g + e = r$ (`hr`) and a finite index type $\iota$.
--
--   The hypotheses are the following groups.
--
--   Cohomological normalisation: `hH0` states that for every $R$-algebra $A$ the structure map $A \to \Gamma(C \times_R \operatorname{Spec} A, \top)$ is bijective, i.e. $c_*\mathcal O_C = \mathcal O$ holds universally after base change to affines. `hg` states that for every algebraically closed field $k$, every $x \colon \operatorname{Spec} k \to \operatorname{Spec} R$ and every two-affine open cover of the fibre, the first two-chart Čech cohomology of the unit module has $k$-dimension $g$ (so $g$ is the genus of the geometric fibres, computed from the Čech complex of the cover).
--
--   Finite presentation: `hlfp` is `AffineLimit.IsLFPSurj` for the cut Picard presheaf: every element over $\operatorname{Spec} A$, for $A$ an $R$-algebra, comes from an element over $\operatorname{Spec} A_0$ for some finitely generated $R$-subalgebra $A_0 \subseteq A$.
--
--   The smooth locus: $U$ is an open subscheme of $C$ with $U \hookrightarrow C$ followed by $c$ smooth of relative dimension $1$, and `hεU` requires the image of $\varepsilon$ to lie in $U$. A relative effective Cartier divisor $D$ (an ideal sheaf data on $C \times_R T$ whose closed subscheme is finite, flat and locally of finite presentation over $T$ of constant rank) is `SupportedIn U` when the support of its ideal lies in the preimage of $U$.
--
--   The universal divisor data: $Y$ is a scheme with $y \colon Y \to \operatorname{Spec} R$ locally of finite type and $Y$ quasi-compact, $D^{\mathrm{univ}}$ is a relative effective Cartier divisor of degree $g$ over $y$ with `hDunivU` asserting that it is supported in $U$, and `huniv` asserts that for every $T$, every $g' \colon T \to \operatorname{Spec} R$ and every relative effective Cartier divisor $D$ of degree $g$ over $g'$ supported in $U$ there is exactly one morphism $\varphi \colon T \to Y$ over $\operatorname{Spec} R$ along which $D^{\mathrm{univ}}$ pulls back to $D$ (equality of the comapped ideals).
--
--   The section hypothesis `hsect`: for every $u \colon V \to \operatorname{Spec} R$ locally of finite type and every invertible module $M$ on $C \times_R V$ such that (i) on all field-valued fibres the Čech $H^1$ of $M$ vanishes and the Čech $H^0$ has dimension $1$, and (ii) for every algebraically closed field $k$, every $x \colon \operatorname{Spec} k \to V$ and every nonzero morphism $\sigma$ from the unit module to the pullback of $M$ to $C_{x \circ u}$ there is a relative effective Cartier divisor of degree $g$ over $x \circ u$ whose ideal is the zero-scheme ideal of $\sigma$ and which is supported in $U$, there exist a relative effective Cartier divisor $D_0$ of degree $g$ over $u$ and an invertible module $N$ on $V$ with $\mathcal O(D_0) \cong M \otimes \pi^* N$ ($\pi$ the projection $C \times_R V \to V$), and moreover any relative effective Cartier divisor $D'$ of any degree $d'$ over $u$ which is supported in $U$ and satisfies $\mathcal O(D') \cong M \otimes \pi^* N'$ for some invertible $N'$ has the same ideal as $D_0$.
--
--   The chart divisors: $D_{\gamma} \colon \iota \to$ relative effective Cartier divisors of degree $e$ over the identity of $\operatorname{Spec} R$, with `hDγU` asserting that each is supported in $U$. Here `sectionTwist c ε t r` is the dual of the $r$-th power of the ideal of the rigidifying section, so that $L.L \otimes (\mathrm{sectionTwist} \otimes (D_{\gamma i})_T\text{'s ideal module})$ is the twist $L(r\varepsilon - D_{\gamma i})$ on $C \times_R T$. Five hypotheses govern these charts:
--
--   `hχ`: for each $i$, each algebraically closed field $k$, each $x \colon \operatorname{Spec} k \to \operatorname{Spec} R$ and each two-affine cover of the fibre, the difference $\dim_k H^0 - \dim_k H^1$ of the two-chart Čech complex of the fibre of $\mathcal O(r\varepsilon) \otimes I_{D_{\gamma i}}$ equals $1$.
--
--   `hZfibγ`: for each $i$, each $t \colon T \to \operatorname{Spec} R$ locally of finite type and each rigidified line bundle $L$ over $t$ in the cut, for every algebraically closed field $k$, every $x \colon \operatorname{Spec} k \to T$ and every nonzero section $\sigma$ of the pullback of $L(r\varepsilon - D_{\gamma i})$ to $C_{x \circ t}$, there is a relative effective Cartier divisor of degree $g$ over $x \circ t$ whose ideal is the zero-scheme ideal of $\sigma$ and which is supported in $U$.
--
--   `hH0one`: for each $i$, each $t \colon T \to \operatorname{Spec} R$, each rigidified line bundle $L$ over $t$ in the cut, each field $k$, each $s \colon \operatorname{Spec} k \to T$ and each two-affine cover of the fibre, vanishing of the Čech $H^1$ of the fibre of $L(r\varepsilon - D_{\gamma i})$ forces its Čech $H^0$ to have dimension $1$.
--
--   `hcover`: for each $t \colon T \to \operatorname{Spec} R$, each rigidified line bundle $L$ over $t$ in the cut, each field $k$ and each $s \colon \operatorname{Spec} k \to T$, there is an index $i$ for which the Čech $H^1$ of the fibre of $L(r\varepsilon - D_{\gamma i})$ vanishes for every two-affine cover.
--
--   `havoid`: for each $i$, each $t \colon T \to \operatorname{Spec} R$ locally of finite type, each rigidified line bundle $L$ over $t$ in the cut, each relative effective Cartier divisor $D_0$ of degree $g$ over $t$ and each invertible $N$ on $T$, an isomorphism $\mathcal O(D_0) \cong L(r\varepsilon - D_{\gamma i}) \otimes \pi^* N$ forces $D_0$ to be supported in $U$.
--
--   `hcut`: for each $i$, each $t \colon T \to \operatorname{Spec} R$ locally of finite type, each relative effective Cartier divisor $D$ of degree $r$ and each $D_0$ of degree $g$ over $t$ with $D_0$ supported in $U$ and $I_D = I_{D_0} \cdot I_{(D_{\gamma i})_T}$, there is an open subscheme $W \subseteq T$ such that for every algebraically closed field $k$ and every $s \colon \operatorname{Spec} k \to T$ the image of $s$ lies in $W$ if and only if the restriction to the fibre of the rigidified twist `D.twistModule c ε` satisfies `IsAlgEquivZero`.
--
--   Under these hypotheses there exist schemes $X_i$ ($i \in \iota$) and morphisms of presheaves $f_i$ from the ULift-Yoneda presheaf of $X_i$ to the `overTotal` presheaf of the cut relative Picard functor such that all of the following hold: each $f_i$ is an open immersion in the relative sense `MorphismProperty.presheafULift @IsOpenImmersion` with respect to ULift-Yoneda; the structure morphism $X_i \to \operatorname{Spec} R$ corresponding to $f_i$ under `uliftYonedaEquiv` is locally of finite type; each $X_i$ is quasi-compact; the morphism `Limits.Sigma.desc f` from the coproduct of the $\mathrm{ULift}$-Yoneda presheaves of the $X_i$ to the `overTotal` presheaf is locally surjective for the Zariski topology; for every $i$, every scheme $T$, every element $x$ of the `overTotal` presheaf at $T$ whose structure morphism $T \to \operatorname{Spec} R$ is locally of finite type, every rigidified line bundle $L$ over that structure morphism whose class is the relative Picard element underlying $x$, every field $k$ and every $s \colon \operatorname{Spec} k \to T$ for which the Čech $H^1$ of the fibre of $L(r\varepsilon - D_{\gamma i})$ vanishes for every two-affine cover of that fibre, the point $s$ factors through the $i$-th chart, i.e. there is $\varphi' \colon \operatorname{Spec} k \to X_i$ with $\varphi'$ followed by $f_i$ equal to $s$ followed by $x$ (after applying ULift-Yoneda to $\varphi'$ and to $s$); and finally, each $X_i$ admits an open immersion $j \colon X_i \to Y$ into the scheme of degree-$g$ divisors with $j$ followed by $y$ equal to the structure morphism of $X_i$.
--
--   This is the chart-construction step for the relative $\operatorname{Pic}^0$ of a proper flat pointed curve whose chart divisors are constrained to lie in the relative smooth locus $U$, so that semistable curves (for instance Deligne–Rapoport models) may be used: the charts are Milne's $J^{\gamma}$, realised as open subschemes of the scheme of relative effective divisors of degree $g$ supported in $U$. Its conclusion is precisely the charts input of the representability results [`AlgebraicGeometry.RelPicard.exists_representsRelSubPic_algEquivZeroCut_of_chartData`](thm.html#AlgebraicGeometry.RelPicard.exists_representsRelSubPic_algEquivZeroCut_of_chartData) and [`AlgebraicGeometry.RelPicard.forall_prime_exists_representsRelSubPic_algEquivZeroCut_baseChange_away_of_smoothLocus_of_twoLineDegenerations`](thm.html#AlgebraicGeometry.RelPicard.forall_prime_exists_representsRelSubPic_algEquivZeroCut_baseChange_away_of_smoothLocus_of_twoLineDegenerations).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_openCharts_relSubPicPresheaf_algEquivZeroCut_of_relEffCartierDiv_supportedIn_of_fibrewise_zeroScheme.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra

theorem AlgebraicGeometry.RelPicard.exists_openCharts_relSubPicPresheaf_algEquivZeroCut_of_relEffCartierDiv_supportedIn_of_fibrewise_zeroScheme
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [Flat c] (𝒱 : C.TwoAffineOpenCover)
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)

    (hlfp : AffineLimit.IsLFPSurj (relSubPicPresheaf c ε (algEquivZeroCut c ε)))

    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (hεU : Set.range ε.1 ⊆ (U : Set C))

    {ι : Type u} [Finite ι] (g e r : ℕ) (hr : g + e = r)

    (hg : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover),
      Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
        (𝟙_ (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).Modules)).H1 = g)

    (Y : Scheme.{u}) (y : Y ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType y] [CompactSpace Y]
    (Duniv : RelEffCartierDiv c g y) (hDunivU : Duniv.SupportedIn U)
    (huniv : ∀ ⦃T : Scheme.{u}⦄ (g' : T ⟶ Spec (CommRingCat.of R)) (D : RelEffCartierDiv c g g'), D.SupportedIn U →
        ∃! φ : {φ : T ⟶ Y // φ ≫ y = g'}, PullsBackOver Duniv φ.1 φ.2 D)

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
    (Dγ : ι → RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R))))
    (hDγU : ∀ i, (Dγ i).SupportedIn U)

    (hχ : ∀ (i : ι) (k : Type u) [Field k] [IsAlgClosed k]
      (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover),
      (Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ (Dγ i).idealModule))).H0 : ℤ) -
        Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ (Dγ i).idealModule))).H1 = 1)

    (hZfibγ : ∀ (i : ι) ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
      (L : RigidifiedLineBundle c ε t), FibrewiseAlgEquivZero L →
      ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ T)
        (σ : 𝟙_ (pullback c (x ≫ t)).Modules ⟶ (Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj
          (L.L ⊗ (sectionTwist c ε t r ⊗ ((Dγ i).pullbackAlong t (Category.comp_id t)).idealModule))), σ ≠ 0 →
        ∃ Dx : RelEffCartierDiv c g (x ≫ t), Dx.I = Scheme.Modules.zeroSchemeIdeal σ ∧ Dx.SupportedIn U)

    (hH0one : ∀ (i : ι) ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) (L : RigidifiedLineBundle c ε t), FibrewiseAlgEquivZero L →
      ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T) (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          (L.L ⊗ (sectionTwist c ε t r ⊗ ((Dγ i).pullbackAlong t (Category.comp_id t)).idealModule)))).H1 →
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          (L.L ⊗ (sectionTwist c ε t r ⊗ ((Dγ i).pullbackAlong t (Category.comp_id t)).idealModule)))).H0 = 1)

    (hcover : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) (L : RigidifiedLineBundle c ε t),
      FibrewiseAlgEquivZero L → ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T),
      ∃ i : ι, ∀ (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          (L.L ⊗ (sectionTwist c ε t r ⊗ ((Dγ i).pullbackAlong t (Category.comp_id t)).idealModule)))).H1)

    (havoid : ∀ (i : ι) ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
      (L : RigidifiedLineBundle c ε t), FibrewiseAlgEquivZero L →
      ∀ (D₀ : RelEffCartierDiv c g t) (N : T.Modules), Scheme.Modules.IsInvertible N →
        Nonempty (D₀.lineBundle ≅
          (L.L ⊗ (sectionTwist c ε t r ⊗ ((Dγ i).pullbackAlong t (Category.comp_id t)).idealModule)) ⊗
            (Scheme.Modules.pullback (pullback.snd c t)).obj N) →
        D₀.SupportedIn U)

    (hcut : ∀ (i : ι) ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
      (D : RelEffCartierDiv c r t) (D₀ : RelEffCartierDiv c g t), D₀.SupportedIn U →
      D.I = D₀.I * ((Dγ i).pullbackAlong t (Category.comp_id t)).I →
      ∃ W : T.Opens, ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T),
        Set.range ⇑s ⊆ (W : Set T) ↔
          IsAlgEquivZero (fibreAt c t s)
            ((Scheme.Modules.pullback (pullback.fst (pullback.snd c t) s)).obj (D.twistModule c ε))) :
    ∃ (X : ι → Scheme.{u})
      (f : ∀ i, uliftYoneda.{u + 1}.obj (X i) ⟶ (relSubPicPresheaf c ε (algEquivZeroCut c ε)).overTotal),
      (∀ i, MorphismProperty.presheafULift.{u + 1} @IsOpenImmersion (f i)) ∧
      (∀ i, LocallyOfFiniteType (uliftYonedaEquiv (f i)).1) ∧
      (∀ i, CompactSpace (X i)) ∧
      Presheaf.IsLocallySurjective Scheme.zariskiTopology (Limits.Sigma.desc f) ∧

      (∀ (i : ι) ⦃T : Scheme.{u}⦄
        (x : uliftYoneda.{u + 1}.obj T ⟶ (relSubPicPresheaf c ε (algEquivZeroCut c ε)).overTotal),
        LocallyOfFiniteType (uliftYonedaEquiv x).1 →
        ∀ (L : RigidifiedLineBundle c ε (uliftYonedaEquiv x).1), Quotient.mk _ L = (uliftYonedaEquiv x).2.1 →
        ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T),
          (∀ (𝒲 : (pullback (pullback.snd c (uliftYonedaEquiv x).1) s).TwoAffineOpenCover),
            Subsingleton (𝒲.sectionsOf (fibreAt c (uliftYonedaEquiv x).1 s) (fibreModule c (uliftYonedaEquiv x).1 s
              (L.L ⊗ (sectionTwist c ε (uliftYonedaEquiv x).1 r ⊗
                ((Dγ i).pullbackAlong (uliftYonedaEquiv x).1 (Category.comp_id _)).idealModule)))).H1) →
          ∃ φ' : Spec (CommRingCat.of k) ⟶ X i,
            uliftYoneda.{u + 1}.map φ' ≫ f i = uliftYoneda.{u + 1}.map s ≫ x) ∧

      (∀ i, ∃ j : X i ⟶ Y, IsOpenImmersion j ∧ j ≫ y = (uliftYonedaEquiv (f i)).1) := by sorry
