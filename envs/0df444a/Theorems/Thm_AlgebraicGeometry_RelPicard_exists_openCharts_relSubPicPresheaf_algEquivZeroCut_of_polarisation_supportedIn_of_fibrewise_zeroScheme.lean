-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_openCharts_relSubPicPresheaf_algEquivZeroCut_of_polarisation_supportedIn_of_fibrewise_zeroScheme
-- name    : AlgebraicGeometry.RelPicard.exists_openCharts_relSubPicPresheaf_algEquivZeroCut_of_polarisation_supportedIn_of_fibrewise_zeroScheme
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/2b8cf9a6-aed8-5b6d-8e6e-ea780d005d32
-- title:
--   Polarised open charts of the relative Pic⁰ presheaf
-- statement:
--   Throughout, $R$ is a Noetherian commutative ring, $c\colon C\to\operatorname{Spec}R$ is a proper flat morphism of schemes, $\mathcal V$ is a two-affine open cover of $C$ (two affine opens $U_0,U_1$ with $U_0\sqcup U_1=\top$ and $U_0\cap U_1$ affine), and $\varepsilon$ is a section of $c$, i.e. a morphism $\operatorname{Spec}R\to C$ with $\varepsilon\circ$-composite $c$ equal to the identity. The hypothesis `hH0` requires that for every $R$-algebra $A$ the structural map $A\to\Gamma(C\times_{\operatorname{Spec}R}\operatorname{Spec}A,\top)$ be bijective, the algebra structure being the one induced by the projection to $\operatorname{Spec}A$. The presheaf under study is `relSubPicPresheaf c ε (algEquivZeroCut c ε)` on $(\mathrm{Over}\ \operatorname{Spec}R)^{\mathrm{op}}$: the subfunctor of the relative Picard presheaf of $(c,\varepsilon)$ cut out by the condition `FibrewiseAlgEquivZero`, namely that a rigidified line bundle $L$ on $C_T=C\times_{\operatorname{Spec}R}T$ satisfy, for every algebraically closed field $k$ and every $s\colon\operatorname{Spec}k\to T$, the predicate `IsAlgEquivZero` for the pullback of $L$ to the fibre over $s$ (existence of a geometrically integral parameter scheme of finite type over $k$, an invertible module on the corresponding product, and two sections over $k$ along which that module becomes the unit, respectively the pullback of $L$). Its `overTotal` is the presheaf on schemes sending $T$ to the pairs consisting of a morphism $t\colon T\to\operatorname{Spec}R$ and an element of the presheaf at $\mathrm{Over.mk}\ t$. The hypothesis `hlfp` asserts `AffineLimit.IsLFPSurj` for this presheaf: every element over $\operatorname{Spec}A$, $A$ an $R$-algebra, is the image of an element over $\operatorname{Spec}A_0$ for some finitely generated $R$-subalgebra $A_0\subseteq A$.
--
--   Further data: an open $U\subseteq C$ with $U\hookrightarrow C\to\operatorname{Spec}R$ smooth of relative dimension $1$, such that the range of $\varepsilon$ lies in $U$ (`hεU`); a finite index type $\iota$; natural numbers $g,e,\rho$ with $g+e=\rho$ (`hr`). Here a term of `RelEffCartierDiv c r t` consists of an ideal sheaf datum $I$ on $C_T$ whose closed subscheme is finite, flat and locally of finite presentation over $T$ with fibre rank identically $r$; `SupportedIn U` means that the support of $I$ is contained in the preimage of $U$ under the projection $C_T\to C$; `idealModule` denotes the module $I$ and `lineBundle` its dual. The polarisation is $E\in$ `RelEffCartierDiv c ρ (𝟙 (Spec R))`, supported in $U$ (`hEU`).
--
--   The fibrewise genus hypothesis `hg` requires that for every algebraically closed field $k$, every $x\colon\operatorname{Spec}k\to\operatorname{Spec}R$ and every two-affine open cover $\mathcal W$ of the corresponding fibre, the $k$-dimension of the first two-chart Čech cohomology $H^1$ of the unit module equal $g$.
--
--   The divisor scheme is given as data: $Y$ with $y\colon Y\to\operatorname{Spec}R$ locally of finite type and $Y$ quasi-compact, a divisor $D_{\mathrm{univ}}\in$ `RelEffCartierDiv c g y` supported in $U$ (`hDunivU`), and the universal property `huniv`: for every $T$, every $g'\colon T\to\operatorname{Spec}R$ and every $D\in$ `RelEffCartierDiv c g g'` supported in $U$ there is a unique morphism $\varphi\colon T\to Y$ over $\operatorname{Spec}R$ along which $D_{\mathrm{univ}}$ pulls back to $D$.
--
--   The hypothesis `hsect` is the section-to-divisor principle: for every $V$, every locally-of-finite-type $u\colon V\to\operatorname{Spec}R$ and every invertible module $M$ on $C_V$ such that (i) for every field $k$, every $s\colon\operatorname{Spec}k\to V$ and every two-affine cover of the fibre, the $H^1$ of the fibre sections of $M$ is subsingleton and the $H^0$ has $k$-dimension $1$, and (ii) for every algebraically closed $k$, every $x\colon\operatorname{Spec}k\to V$ and every nonzero morphism $\sigma$ from the unit module to the pullback of $M$ to the fibre product over $x$, the zero-scheme ideal `zeroSchemeIdeal σ` is the ideal of some divisor in `RelEffCartierDiv c g (x ≫ u)` supported in $U$ — there exist $D_0\in$ `RelEffCartierDiv c g u` and an invertible module $N$ on $V$ with $D_0$'s line bundle isomorphic to $M$ tensored with the pullback of $N$ along $C_V\to V$, and moreover, for every $d'$, every $D'\in$ `RelEffCartierDiv c d' u` supported in $U$ and every invertible $N'$ on $V$ with $D'$'s line bundle isomorphic to $M$ tensored with the pullback of $N'$, one has $D'.I=D_0.I$.
--
--   Finally, a family $D_\gamma\colon\iota\to$ `RelEffCartierDiv c e (𝟙 (Spec R))` is given, each $D_{\gamma_i}$ supported in $U$ (`hDγU`). For a rigidified line bundle $L$ on $C_T$ write $M_i(L)=L\otimes\big(\mathcal O(E_T)\otimes\mathcal I(D_{\gamma_i,T})\big)$, where $E_T$ and $D_{\gamma_i,T}$ are the pullbacks of $E$ and $D_{\gamma_i}$ along $t$, $\mathcal O(E_T)$ is the line bundle (dual ideal module) of $E_T$ and $\mathcal I(D_{\gamma_i,T})$ the ideal module of $D_{\gamma_i,T}$. The remaining hypotheses, all indexed by $i\in\iota$ except `hcover`, concern this twist:
--
--   `hχ` (Euler characteristic): for every $i$, every algebraically closed $k$, every $x\colon\operatorname{Spec}k\to\operatorname{Spec}R$ and every two-affine cover of the fibre, $\dim_k H^0-\dim_k H^1$ of the fibre sections of $\mathcal O(E)\otimes\mathcal I(D_{\gamma_i})$ equals $1$.
--
--   `hZfibγ` (zero schemes are divisors): for every $i$, every $T$, every locally-of-finite-type $t\colon T\to\operatorname{Spec}R$ and every rigidified line bundle $L$ on $C_T$ satisfying `FibrewiseAlgEquivZero`, and for every algebraically closed $k$, every $x\colon\operatorname{Spec}k\to T$ and every nonzero $\sigma$ from the unit module to the pullback of $M_i(L)$ to the fibre product over $x$ whose zero-scheme ideal has support inside the preimage of $U$: that zero-scheme ideal is the ideal of some divisor in `RelEffCartierDiv c g (x ≫ t)` supported in $U$.
--
--   `hH0one` ($h^0=1$): for every $i$, every $t\colon T\to\operatorname{Spec}R$, every rigidified $L$ satisfying `FibrewiseAlgEquivZero`, every field $k$, every $s\colon\operatorname{Spec}k\to T$ and every two-affine cover of the fibre, vanishing of $H^1$ (subsingleton) for the fibre sections of $M_i(L)$ implies that the $H^0$ has $k$-dimension $1$.
--
--   `hcover` (the family of twists suffices): for every $t\colon T\to\operatorname{Spec}R$, every rigidified $L$ satisfying `FibrewiseAlgEquivZero`, every field $k$ and every $s\colon\operatorname{Spec}k\to T$ there is an index $i\in\iota$ such that, for every two-affine cover of the fibre, the $H^1$ of the fibre sections of $M_i(L)$ is subsingleton, and every nonzero $\sigma$ from the unit module to the pullback of $M_i(L)$ over $s$ has zero-scheme ideal supported inside the preimage of $U$.
--
--   `havoid` (the produced divisor stays in $U$): for every $i$, every locally-of-finite-type $t$ and every rigidified $L$ satisfying `FibrewiseAlgEquivZero` for which all nonzero sections of $M_i(L)$ over algebraically closed points have zero-scheme support inside the preimage of $U$: every $D_0\in$ `RelEffCartierDiv c g t` whose line bundle is isomorphic to $M_i(L)$ tensored with the pullback of an invertible module $N$ on $T$ is supported in $U$.
--
--   `hcut` (openness of the algebraic-equivalence condition): for every $i$, every locally-of-finite-type $t\colon T\to\operatorname{Spec}R$, every $D\in$ `RelEffCartierDiv c ρ t` and every $D_0\in$ `RelEffCartierDiv c g t` supported in $U$ with $D.I=D_0.I\cdot \mathcal I(D_{\gamma_i,T})$'s ideal, there is an open $W\subseteq T$ such that for every algebraically closed $k$ and every $s\colon\operatorname{Spec}k\to T$, the range of $s$ lies in $W$ if and only if the fibre over $s$ of the rigidification (along `rigSection c t ε` and the projection $C_T\to T$) of $\mathcal O(D)\otimes\mathcal I(E_T)$ satisfies `IsAlgEquivZero`.
--
--   Under these hypotheses there exist a family of schemes $X\colon\iota\to\mathrm{Scheme}$ and morphisms of presheaves $f_i$ from the (lifted) Yoneda presheaf of $X_i$ to `(relSubPicPresheaf c ε (algEquivZeroCut c ε)).overTotal` such that:
--
--   1. each $f_i$ belongs to `MorphismProperty.presheafULift @IsOpenImmersion`, the relativisation of open immersions along the lifted Yoneda embedding;
--
--   2. for each $i$, the structure morphism $X_i\to\operatorname{Spec}R$ underlying $f_i$, i.e. the first component of `uliftYonedaEquiv (f i)`, is locally of finite type;
--
--   3. each $X_i$ is quasi-compact;
--
--   4. the induced morphism `Limits.Sigma.desc f` from the coproduct of the $\mathrm{Yoneda}(X_i)$ to `overTotal` is locally surjective for the Zariski topology;
--
--   5. the charts capture all fibrewise-admissible points: for every $i$, every scheme $T$ and every $x$ from the lifted Yoneda presheaf of $T$ to `overTotal` whose underlying morphism $T\to\operatorname{Spec}R$ is locally of finite type, every rigidified line bundle $L$ on $C_T$ whose class in the relative Picard presheaf is the second component of $x$, every field $k$ and every $s\colon\operatorname{Spec}k\to T$ such that (a) for every two-affine cover of the fibre over $s$ the $H^1$ of the fibre sections of $M_i(L)$ is subsingleton, and (b) every nonzero $\sigma$ from the unit module to the pullback of $M_i(L)$ over $s$ has zero-scheme ideal supported inside the preimage of $U$, there is a morphism $\varphi'\colon\operatorname{Spec}k\to X_i$ with $\mathrm{Yoneda}(\varphi')$ followed by $f_i$ equal to $\mathrm{Yoneda}(s)$ followed by $x$;
--
--   6. each $X_i$ is an open subscheme of the divisor scheme $Y$: there is an open immersion $j\colon X_i\to Y$ with $j$ followed by $y$ equal to the structure morphism of $X_i$ over $\operatorname{Spec}R$.
--
--   This is the polarised form of Milne's construction of open charts of the relative $\mathrm{Pic}^0$ of a proper flat curve with a section, the charts being cut out inside the relative smooth locus $U$ and parametrised by divisors of degree $g$ there; the twist by a single multiple of the section is replaced by an arbitrary relative effective Cartier divisor $E$ supported in $U$, together with a finite family of auxiliary divisors $D_{\gamma_i}$ of complementary degree. It supplies the chart data used by [`AlgebraicGeometry.RelPicard.forall_prime_exists_representsRelSubPic_algEquivZeroCut_baseChange_away_of_smoothLocus_of_twoGluedSmoothCurveDegenerations`](thm.html#AlgebraicGeometry.RelPicard.forall_prime_exists_representsRelSubPic_algEquivZeroCut_baseChange_away_of_smoothLocus_of_twoGluedSmoothCurveDegenerations) on the way to representability of the relative $\mathrm{Pic}^0$ functor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_openCharts_relSubPicPresheaf_algEquivZeroCut_of_polarisation_supportedIn_of_fibrewise_zeroScheme.lean

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

theorem AlgebraicGeometry.RelPicard.exists_openCharts_relSubPicPresheaf_algEquivZeroCut_of_polarisation_supportedIn_of_fibrewise_zeroScheme
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

    {ι : Type u} [Finite ι] (g e ρ : ℕ) (hr : g + e = ρ)

    (E : RelEffCartierDiv c ρ (𝟙 (Spec (CommRingCat.of R)))) (hEU : E.SupportedIn U)

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
          (fibreModule c (𝟙 _) x (E.lineBundle ⊗ (Dγ i).idealModule))).H0 : ℤ) -
        Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (E.lineBundle ⊗ (Dγ i).idealModule))).H1 = 1)

    (hZfibγ : ∀ (i : ι) ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
      (L : RigidifiedLineBundle c ε t), FibrewiseAlgEquivZero L →
      ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ T)
        (σ : 𝟙_ (pullback c (x ≫ t)).Modules ⟶ (Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj
          (L.L ⊗ ((E.pullbackAlong t (Category.comp_id t)).lineBundle ⊗ ((Dγ i).pullbackAlong t (Category.comp_id t)).idealModule))), σ ≠ 0 →

        ((Scheme.Modules.zeroSchemeIdeal σ).support : Set ↥(pullback c (x ≫ t))) ⊆ ((pullback.fst c (x ≫ t)) ⁻¹ᵁ U : Set ↥(pullback c (x ≫ t))) →
        ∃ Dx : RelEffCartierDiv c g (x ≫ t), Dx.I = Scheme.Modules.zeroSchemeIdeal σ ∧ Dx.SupportedIn U)

    (hH0one : ∀ (i : ι) ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) (L : RigidifiedLineBundle c ε t), FibrewiseAlgEquivZero L →
      ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T) (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          (L.L ⊗ ((E.pullbackAlong t (Category.comp_id t)).lineBundle ⊗ ((Dγ i).pullbackAlong t (Category.comp_id t)).idealModule)))).H1 →
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          (L.L ⊗ ((E.pullbackAlong t (Category.comp_id t)).lineBundle ⊗ ((Dγ i).pullbackAlong t (Category.comp_id t)).idealModule)))).H0 = 1)

    (hcover : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) (L : RigidifiedLineBundle c ε t),
      FibrewiseAlgEquivZero L → ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T),
      ∃ i : ι, (∀ (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          (L.L ⊗ ((E.pullbackAlong t (Category.comp_id t)).lineBundle ⊗ ((Dγ i).pullbackAlong t (Category.comp_id t)).idealModule)))).H1) ∧

        (∀ σ : 𝟙_ (pullback c (s ≫ t)).Modules ⟶ (Scheme.Modules.pullback (mapOnProdOver c s rfl)).obj
            (L.L ⊗ ((E.pullbackAlong t (Category.comp_id t)).lineBundle ⊗ ((Dγ i).pullbackAlong t (Category.comp_id t)).idealModule)),
          σ ≠ 0 → ((Scheme.Modules.zeroSchemeIdeal σ).support : Set ↥(pullback c (s ≫ t))) ⊆ ((pullback.fst c (s ≫ t)) ⁻¹ᵁ U : Set ↥(pullback c (s ≫ t)))))

    (havoid : ∀ (i : ι) ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
      (L : RigidifiedLineBundle c ε t), FibrewiseAlgEquivZero L →

      (∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ T)
        (σ : 𝟙_ (pullback c (x ≫ t)).Modules ⟶ (Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj
          (L.L ⊗ ((E.pullbackAlong t (Category.comp_id t)).lineBundle ⊗ ((Dγ i).pullbackAlong t (Category.comp_id t)).idealModule))),
        σ ≠ 0 → ((Scheme.Modules.zeroSchemeIdeal σ).support : Set ↥(pullback c (x ≫ t))) ⊆ ((pullback.fst c (x ≫ t)) ⁻¹ᵁ U : Set ↥(pullback c (x ≫ t)))) →
      ∀ (D₀ : RelEffCartierDiv c g t) (N : T.Modules), Scheme.Modules.IsInvertible N →
        Nonempty (D₀.lineBundle ≅
          (L.L ⊗ ((E.pullbackAlong t (Category.comp_id t)).lineBundle ⊗ ((Dγ i).pullbackAlong t (Category.comp_id t)).idealModule)) ⊗
            (Scheme.Modules.pullback (pullback.snd c t)).obj N) →
        D₀.SupportedIn U)

    (hcut : ∀ (i : ι) ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
      (D : RelEffCartierDiv c ρ t) (D₀ : RelEffCartierDiv c g t), D₀.SupportedIn U →
      D.I = D₀.I * ((Dγ i).pullbackAlong t (Category.comp_id t)).I →
      ∃ W : T.Opens, ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T),
        Set.range ⇑s ⊆ (W : Set T) ↔
          IsAlgEquivZero (fibreAt c t s)
            ((Scheme.Modules.pullback (pullback.fst (pullback.snd c t) s)).obj (Scheme.Modules.rigidify (RelPicard.rigSection c t ε) (pullback.snd c t)
              (D.lineBundle ⊗ (E.pullbackAlong t (Category.comp_id t)).idealModule)))) :
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
              (L.L ⊗ ((E.pullbackAlong (uliftYonedaEquiv x).1 (Category.comp_id _)).lineBundle ⊗
                ((Dγ i).pullbackAlong (uliftYonedaEquiv x).1 (Category.comp_id _)).idealModule)))).H1) →

          (∀ σ : 𝟙_ (pullback c (s ≫ (uliftYonedaEquiv x).1)).Modules ⟶
              (Scheme.Modules.pullback (mapOnProdOver c s rfl)).obj
                (L.L ⊗ ((E.pullbackAlong (uliftYonedaEquiv x).1 (Category.comp_id _)).lineBundle ⊗
                  ((Dγ i).pullbackAlong (uliftYonedaEquiv x).1 (Category.comp_id _)).idealModule)),
            σ ≠ 0 → ((Scheme.Modules.zeroSchemeIdeal σ).support : Set ↥(pullback c (s ≫ (uliftYonedaEquiv x).1))) ⊆
              ((pullback.fst c (s ≫ (uliftYonedaEquiv x).1)) ⁻¹ᵁ U : Set ↥(pullback c (s ≫ (uliftYonedaEquiv x).1)))) →
          ∃ φ' : Spec (CommRingCat.of k) ⟶ X i,
            uliftYoneda.{u + 1}.map φ' ≫ f i = uliftYoneda.{u + 1}.map s ≫ x) ∧

      (∀ i, ∃ j : X i ⟶ Y, IsOpenImmersion j ∧ j ≫ y = (uliftYonedaEquiv (f i)).1) := by sorry
