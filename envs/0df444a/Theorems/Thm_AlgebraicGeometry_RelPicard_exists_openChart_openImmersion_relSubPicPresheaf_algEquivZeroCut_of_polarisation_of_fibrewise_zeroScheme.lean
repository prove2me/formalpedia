-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_polarisation_of_fibrewise_zeroScheme
-- name    : AlgebraicGeometry.RelPicard.exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_polarisation_of_fibrewise_zeroScheme
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/538b98dd-1b78-546e-9060-89e069d59dab
-- title:
--   A polarised open chart for the relative Pic⁰ subfunctor
-- statement:
--   Throughout, $R$ is a Noetherian commutative ring and $c\colon C\to\operatorname{Spec}R$ is a proper flat morphism of schemes, equipped with a two-affine open cover $\mathcal V$ of $C$ (two affine opens $\mathcal V.U_0,\mathcal V.U_1$ with union $C$ and affine intersection). The hypothesis `hH0` requires cohomological flatness in degree $0$ in the strong form: for every $R$-algebra $A$, the structural map $A\to\Gamma(C\times_{\operatorname{Spec}R}\operatorname{Spec}A,\top)$ (the $R$-algebra structure on the global sections being the one induced by the second projection) is bijective. Further, $\varepsilon$ is a section of $c$, i.e. a morphism $\varepsilon\colon\operatorname{Spec}R\to C$ with $\varepsilon$ followed by $c$ the identity, and $U\subseteq C$ is an open subscheme whose inclusion followed by $c$ is smooth of relative dimension $1$; `hεU` requires the set-theoretic range of $\varepsilon$ to lie in $U$.
--
--   Natural numbers $g,e,\rho$ are fixed with $g+e=\rho$. The divisor $E$ is a relative effective Cartier divisor of degree $\rho$ for $c$ over the identity of $\operatorname{Spec}R$ — an ideal sheaf datum on $C\times_{\operatorname{Spec}R}\operatorname{Spec}R$ whose closed subscheme is finite, flat and of locally finite presentation over the base with all fibre ranks $\rho$ — and `hEU` requires $E$ to be supported in $U$, i.e. the support of its ideal to lie in the preimage of $U$ under the first projection. For a divisor $D$ the notation $D.\mathtt{idealModule}$ stands for the ideal sheaf viewed as a module (so $\mathcal O(-D)$) and $D.\mathtt{lineBundle}$ for its dual (so $\mathcal O(D)$). The hypothesis `hg` fixes the genus: for every algebraically closed field $k$, every $x\colon\operatorname{Spec}k\to\operatorname{Spec}R$ and every two-affine open cover $\mathcal W$ of the corresponding fibre product, the $k$-dimension of $\check H^1$ of the two-term Čech complex $\Gamma(M,\mathcal W.U_0)\oplus\Gamma(M,\mathcal W.U_1)\to\Gamma(M,\mathcal W.U_0\cap \mathcal W.U_1)$ attached to $\mathcal W$ and to the monoidal unit module $M$ (the structure sheaf) equals $g$; here $\check H^0$ denotes the kernel and $\check H^1$ the cokernel of that differential, taken over the base field of the fibre.
--
--   A scheme $Y$ with a morphism $y\colon Y\to\operatorname{Spec}R$ locally of finite type and with $Y$ quasi-compact is given, together with a relative effective Cartier divisor $D_{\mathrm{univ}}$ of degree $g$ for $c$ over $y$, supported in $U$ (`hDunivU`), and the universality hypothesis `huniv`: for every scheme $T$, every $g'\colon T\to\operatorname{Spec}R$ and every relative effective Cartier divisor $D$ of degree $g$ over $g'$ supported in $U$, there is a unique morphism $\varphi\colon T\to Y$ with $\varphi$ followed by $y$ equal to $g'$ such that the pullback of the ideal of $D_{\mathrm{univ}}$ along the induced map of products equals the ideal of $D$. Finally $D_\gamma$ is a relative effective Cartier divisor of degree $e$ over the identity of $\operatorname{Spec}R$, supported in $U$ (`hD\gamma`), and `hχ` requires that on every geometric fibre the Euler characteristic of $\mathcal O(E)\otimes\mathcal O(-D_\gamma)$ equals $1$: for every algebraically closed $k$, every $x\colon\operatorname{Spec}k\to\operatorname{Spec}R$ and every two-affine cover $\mathcal W$ of the fibre product, $\dim_k\check H^0-\dim_k\check H^1$ of the Čech complex of the restriction of $E.\mathtt{lineBundle}\otimes D_\gamma.\mathtt{idealModule}$ to the fibre is $1$.
--
--   For a rigidified line bundle $L$ for $c,\varepsilon$ over $t\colon T\to\operatorname{Spec}R$ (an invertible module $L.L$ on $C\times_{\operatorname{Spec}R}T$ together with a trivialisation of its pullback along the section induced by $\varepsilon$) write $M_\gamma(L):=L.L\otimes\bigl(\mathcal O(E_T)\otimes\mathcal O(-D_{\gamma,T})\bigr)$, where $E_T$ and $D_{\gamma,T}$ denote the pullbacks of $E$ and $D_\gamma$ along $t$. The predicate `FibrewiseAlgEquivZero` on $L$ asks that for every algebraically closed $k$ and every $s\colon\operatorname{Spec}k\to T$ the restriction of $L.L$ to the fibre satisfy `IsAlgEquivZero`: there are a geometrically integral scheme locally of finite type over $k$, an invertible module on its product with the fibre, and two $k$-points of the parameter scheme at which that module restricts, respectively, to the unit module and to the pullback of the given bundle.
--
--   Five further hypotheses are assumed. `hsect` (the section-cutting input): for every $V$ and $u\colon V\to\operatorname{Spec}R$ locally of finite type and every invertible module $M$ on $C\times_{\operatorname{Spec}R}V$ such that (i) for every field $k$, every $s\colon\operatorname{Spec}k\to V$ and every two-affine cover of the fibre, $\check H^1$ of $M$ on the fibre vanishes and $\dim_k\check H^0=1$, and (ii) for every algebraically closed $k$, every $x\colon\operatorname{Spec}k\to V$ and every nonzero morphism $\sigma$ from the unit module to the pullback of $M$ to $C\times_{\operatorname{Spec}R}\operatorname{Spec}k$, the zero-scheme ideal of $\sigma$ is the ideal of some relative effective Cartier divisor of degree $g$ over $x$ followed by $u$, supported in $U$ — there exist a relative effective Cartier divisor $D_0$ of degree $g$ over $u$ and an invertible module $N$ on $V$ with $\mathcal O(D_0)\cong M\otimes p^*N$, $p$ the second projection, and moreover any $D'$ of any degree $d'$ over $u$ supported in $U$ with $\mathcal O(D')\cong M\otimes p^*N'$ for some invertible $N'$ has the same ideal as $D_0$. `hZfibγ` (zero schemes of sections of $M_\gamma$): for every $t\colon T\to\operatorname{Spec}R$ locally of finite type and every rigidified $L$ with `FibrewiseAlgEquivZero`, every algebraically closed $k$, every $x\colon\operatorname{Spec}k\to T$ and every nonzero $\sigma$ from the unit module to the pullback of $M_\gamma(L)$ to the geometric fibre whose zero-scheme ideal has support inside the preimage of $U$, that zero-scheme ideal is the ideal of a relative effective Cartier divisor of degree $g$ over $x$ followed by $t$, supported in $U$. `hH0one`: in the same situation, for every field $k$, every $s\colon\operatorname{Spec}k\to T$ and every two-affine cover of the fibre, vanishing of $\check H^1$ of $M_\gamma(L)$ on that fibre forces $\dim_k\check H^0=1$. `havoid`: for $t$ locally of finite type and $L$ as above, if on every geometric fibre the zero-scheme ideal of every nonzero $\sigma$ as in `hZfibγ` has support inside the preimage of $U$, then every relative effective Cartier divisor $D_0$ of degree $g$ over $t$ admitting an isomorphism $\mathcal O(D_0)\cong M_\gamma(L)\otimes p^*N$ with $N$ invertible on $T$ is supported in $U$. `hcut`: for $t$ locally of finite type, every relative effective Cartier divisor $D$ of degree $\rho$ over $t$ and every $D_0$ of degree $g$ over $t$ supported in $U$ with ideal identity $D.I=D_0.I\cdot D_{\gamma,T}.I$, there is an open $W\subseteq T$ such that for every algebraically closed $k$ and every $s\colon\operatorname{Spec}k\to T$, the range of $s$ lies in $W$ if and only if the restriction to the fibre over $s$ of the rigidification along $\varepsilon$ of $\mathcal O(D)\otimes\mathcal O(-E_T)$ — that is, of $\bigl(\mathcal O(D)\otimes\mathcal O(-E_T)\bigr)\otimes p^*\bigl(\text{dual of its restriction along the }\varepsilon\text{-section}\bigr)$ — satisfies `IsAlgEquivZero` over $k$.
--
--   Under these assumptions there exist a scheme $X$ and a morphism $f$ from the (ulift) Yoneda presheaf of $X$ to the total-space presheaf of $\mathtt{relSubPicPresheaf}\,c\,\varepsilon\,(\mathtt{algEquivZeroCut}\,c\,\varepsilon)$, the latter being the subfunctor of the relative Picard presheaf of $(c,\varepsilon)$ whose value over $t\colon T\to\operatorname{Spec}R$ consists of the classes of rigidified line bundles that are fibrewise algebraically equivalent to zero, with total space $T\mapsto\sum_{t\colon T\to\operatorname{Spec}R}(\text{such classes over }t)$; the element of the total space corresponding to $f$ under the Yoneda bijection has first component a structure morphism $X\to\operatorname{Spec}R$ and second component a class over it, and the following four assertions hold.
--
--   First, the structure morphism $(\mathtt{uliftYonedaEquiv}\,f).1\colon X\to\operatorname{Spec}R$ is locally of finite type. Second, $X$ is quasi-compact. Third, there is a morphism $j\colon X\to Y$ which is an open immersion and satisfies: $j$ followed by $y$ equals that structure morphism. Fourth, for every scheme $T$ and every morphism $x$ from the Yoneda presheaf of $T$ to the same total-space presheaf whose underlying structure morphism $(\mathtt{uliftYonedaEquiv}\,x).1\colon T\to\operatorname{Spec}R$ is locally of finite type, there exist an open subscheme $U'\subseteq T$ and a morphism $\varphi\colon U'\to X$ such that:
--
--   (a) for every rigidified line bundle $L$ for $c,\varepsilon$ over $(\mathtt{uliftYonedaEquiv}\,x).1$ whose class equals the underlying class of the second component of $x$, and for every field $k$ and every $s\colon\operatorname{Spec}k\to T$, the range of $s$ is contained in $U'$ if and only if both: for every two-affine open cover of the fibre product over $s$, $\check H^1$ of the restriction of $M_\gamma(L)$ to that fibre vanishes; and every nonzero morphism $\sigma$ from the unit module to the pullback of $M_\gamma(L)$ along the map of products induced by $s$ has zero-scheme ideal whose support is contained in the preimage of $U$ under the first projection;
--
--   (b) $\varphi$ followed by $f$ equals the inclusion $U'\hookrightarrow T$ followed by $x$ (after applying the Yoneda embedding to $\varphi$ and to the inclusion);
--
--   (c) $U'$ together with $\varphi$ is final among such factorisations: for every scheme $T'$, every $\psi\colon T'\to T$ and every $\varphi'\colon T'\to X$ with $\psi$ followed by $(\mathtt{uliftYonedaEquiv}\,x).1$ locally of finite type and with $\varphi'$ followed by $f$ equal to $\psi$ followed by $x$, there is a morphism $\chi\colon T'\to U'$ with $\chi$ followed by the inclusion of $U'$ equal to $\psi$ and $\chi$ followed by $\varphi$ equal to $\varphi'$.
--
--   This is one of Milne's charts of the relative $\mathrm{Pic}^0$ built from effective divisors: the twisted bundle $M_\gamma(L)=L\otimes\mathcal O(E_T-D_{\gamma,T})$ has a unique section on the chart, and its zero scheme is a degree-$g$ relative divisor supported in the smooth locus $U$, which identifies the chart with an open subscheme of the scheme $Y$ of such divisors. It feeds [`AlgebraicGeometry.RelPicard.exists_openCharts_relSubPicPresheaf_algEquivZeroCut_of_polarisation_supportedIn_of_fibrewise_zeroScheme`](thm.html#AlgebraicGeometry.RelPicard.exists_openCharts_relSubPicPresheaf_algEquivZeroCut_of_polarisation_supportedIn_of_fibrewise_zeroScheme), where several such charts are assembled into a covering of the subfunctor of fibrewise algebraically trivial rigidified line bundles.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_polarisation_of_fibrewise_zeroScheme.lean

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

theorem AlgebraicGeometry.RelPicard.exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_polarisation_of_fibrewise_zeroScheme
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [Flat c]
    (𝒱 : C.TwoAffineOpenCover)
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)

    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (hεU : Set.range ε.1 ⊆ (U : Set C))

    (g e ρ : ℕ) (hr : g + e = ρ)

    (E : RelEffCartierDiv c ρ (𝟙 (Spec (CommRingCat.of R)))) (hEU : E.SupportedIn U)

    (hg : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover),
      Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
        (𝟙_ (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).Modules)).H1 = g)

    (Y : Scheme.{u}) (y : Y ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType y] [CompactSpace Y]
    (Duniv : RelEffCartierDiv c g y) (hDunivU : Duniv.SupportedIn U)
    (huniv : ∀ ⦃T : Scheme.{u}⦄ (g' : T ⟶ Spec (CommRingCat.of R)) (D : RelEffCartierDiv c g g'), D.SupportedIn U →
        ∃! φ : {φ : T ⟶ Y // φ ≫ y = g'}, PullsBackOver Duniv φ.1 φ.2 D)
    (Dγ : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R))))
    (hDγ : Dγ.SupportedIn U)
    (hχ : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover),
      (Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (E.lineBundle ⊗ Dγ.idealModule))).H0 : ℤ) -
        Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (E.lineBundle ⊗ Dγ.idealModule))).H1 = 1)

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

    (hcut : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
      (D : RelEffCartierDiv c ρ t) (D₀ : RelEffCartierDiv c g t), D₀.SupportedIn U →
      D.I = D₀.I * (Dγ.pullbackAlong t (Category.comp_id t)).I →
      ∃ W : T.Opens, ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T),
        Set.range ⇑s ⊆ (W : Set T) ↔
          IsAlgEquivZero (fibreAt c t s)
            ((Scheme.Modules.pullback (pullback.fst (pullback.snd c t) s)).obj (Scheme.Modules.rigidify (RelPicard.rigSection c t ε) (pullback.snd c t)
              (D.lineBundle ⊗ (E.pullbackAlong t (Category.comp_id t)).idealModule)))) :
    ∃ (X : Scheme.{u}) (f : uliftYoneda.{u + 1}.obj X ⟶ (relSubPicPresheaf c ε (algEquivZeroCut c ε)).overTotal),
      LocallyOfFiniteType (uliftYonedaEquiv f).1 ∧ CompactSpace X ∧
      (∃ j : X ⟶ Y, IsOpenImmersion j ∧ j ≫ y = (uliftYonedaEquiv f).1) ∧
      ∀ ⦃T : Scheme.{u}⦄ (x : uliftYoneda.{u + 1}.obj T ⟶ (relSubPicPresheaf c ε (algEquivZeroCut c ε)).overTotal),
        LocallyOfFiniteType (uliftYonedaEquiv x).1 →
        ∃ (U' : T.Opens) (φ : (↑U' : Scheme.{u}) ⟶ X),
          (∀ (L : RigidifiedLineBundle c ε (uliftYonedaEquiv x).1), Quotient.mk _ L = (uliftYonedaEquiv x).2.1 →
            ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T),
              Set.range ⇑s ⊆ (U' : Set T) ↔
                (∀ (𝒲 : (pullback (pullback.snd c (uliftYonedaEquiv x).1) s).TwoAffineOpenCover),
                  Subsingleton (𝒲.sectionsOf (fibreAt c (uliftYonedaEquiv x).1 s) (fibreModule c (uliftYonedaEquiv x).1 s
                    (L.L ⊗ ((E.pullbackAlong (uliftYonedaEquiv x).1 (Category.comp_id _)).lineBundle ⊗
                      (Dγ.pullbackAlong (uliftYonedaEquiv x).1 (Category.comp_id _)).idealModule)))).H1) ∧

                (∀ σ : 𝟙_ (pullback c (s ≫ (uliftYonedaEquiv x).1)).Modules ⟶
                    (Scheme.Modules.pullback (mapOnProdOver c s rfl)).obj
                      (L.L ⊗ ((E.pullbackAlong (uliftYonedaEquiv x).1 (Category.comp_id _)).lineBundle ⊗
                        (Dγ.pullbackAlong (uliftYonedaEquiv x).1 (Category.comp_id _)).idealModule)),
                  σ ≠ 0 → ((Scheme.Modules.zeroSchemeIdeal σ).support : Set ↥(pullback c (s ≫ (uliftYonedaEquiv x).1))) ⊆
                    ((pullback.fst c (s ≫ (uliftYonedaEquiv x).1)) ⁻¹ᵁ U : Set ↥(pullback c (s ≫ (uliftYonedaEquiv x).1))))) ∧
          uliftYoneda.{u + 1}.map φ ≫ f = uliftYoneda.{u + 1}.map U'.ι ≫ x ∧
          ∀ ⦃T' : Scheme.{u}⦄ (ψ : T' ⟶ T) (φ' : T' ⟶ X),
            LocallyOfFiniteType (ψ ≫ (uliftYonedaEquiv x).1) →
            uliftYoneda.{u + 1}.map φ' ≫ f = uliftYoneda.{u + 1}.map ψ ≫ x →
            ∃ χ : T' ⟶ ↑U', χ ≫ U'.ι = ψ ∧ χ ≫ φ = φ' := by sorry
