-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_fibrewise_zeroScheme
-- name    : AlgebraicGeometry.RelPicard.exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_fibrewise_zeroScheme
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/5d6ce63f-b0f4-54f9-b0ac-dae2a0a16159
-- title:
--   Open chart of the relative Pic⁰ from a universal divisor
-- statement:
--   Let $R$ be a Noetherian commutative ring, $c\colon C\to\operatorname{Spec}R$ a proper flat morphism, $\mathcal V$ a cover of $C$ by two affine opens with affine intersection, and assume that for every $R$-algebra $A$ the structure map $A\to\Gamma(C\times_{\operatorname{Spec}R}\operatorname{Spec}A,\mathcal O)$ is bijective. Let $\varepsilon$ be a section of $c$ over $\operatorname{Spec}R$, let $U\subseteq C$ be open with $U\hookrightarrow C$ followed by $c$ smooth of relative dimension $1$ and with the image of $\varepsilon$ inside $U$, and let $g+e=r$ in $\mathbb N$, where for every algebraically closed field $k$, every $k$-point of $\operatorname{Spec}R$ and every two-affine cover of the corresponding fibre the Čech $H^1$ of the structure sheaf has $k$-dimension $g$. Here a relative effective Cartier divisor of degree $d$ over $t\colon T\to\operatorname{Spec}R$ is an ideal sheaf datum $I$ on $C\times_{\operatorname{Spec}R}T$ whose closed subscheme is finite, flat and locally of finite presentation over $T$ with fibre rank $d$ everywhere, and it is supported in $U$ when the support of $I$ lies in the preimage of $U$ under the first projection. Let $y\colon Y\to\operatorname{Spec}R$ be locally of finite type with $Y$ quasi-compact, carrying a degree-$g$ divisor $\mathcal D$ supported in $U$ which is universal: every degree-$g$ divisor supported in $U$ over any base is the pullback of $\mathcal D$ along a unique morphism over $\operatorname{Spec}R$. Let $D_\gamma$ be a degree-$e$ divisor over $\operatorname{Spec}R$ itself, supported in $U$, such that on every geometric fibre the Čech Euler characteristic $h^0-h^1$ of $\mathcal O(r\varepsilon)\otimes I_{D_\gamma}$ equals $1$; here $\mathcal O(r\varepsilon)$ is the dual of the $r$-th power of the ideal of the rigidifying section and $I_{D_\gamma}$ the ideal module of $D_\gamma$. Five further hypotheses are assumed, stated for the cut $P(L)=$ `FibrewiseAlgEquivZero` $L$, which says that over every algebraically closed field point of the base the fibre of the rigidified line bundle $L$ is algebraically equivalent to zero in the sense of `IsAlgEquivZero` (it is linked to the trivial bundle by an invertible module on the product of the fibre with a geometrically integral base of finite type, evaluated at two sections): (i) a section theorem `hsect`: for $u\colon V\to\operatorname{Spec}R$ locally of finite type and $M$ invertible on $C\times_{\operatorname{Spec}R}V$ with vanishing Čech $H^1$ and $h^0=1$ on all field-valued fibres, and such that every nonzero section of $M$ on a geometric fibre has zero-scheme ideal equal to the ideal of a degree-$g$ divisor supported in $U$, there are a degree-$g$ divisor $D_0$ over $u$ and an invertible $N$ on $V$ with $\mathcal O(D_0)\cong M\otimes\mathrm{pr}_2^*N$, and any divisor $D'$ of any degree supported in $U$ with $\mathcal O(D')\cong M\otimes\mathrm{pr}_2^*N'$ for some invertible $N'$ has $D'.I=D_0.I$; (ii) `hZfibγ`: that zero-scheme premise holds for $L\otimes(\mathcal O(r\varepsilon)\otimes I_{D_\gamma})$ whenever $P(L)$; (iii) `hH0one`: for such bundles, vanishing of the fibrewise Čech $H^1$ forces $h^0=1$; (iv) `havoid`: if $\mathcal O(D_0)\cong (L\otimes(\mathcal O(r\varepsilon)\otimes I_{D_\gamma}))\otimes\mathrm{pr}_2^*N$ with $N$ invertible and $P(L)$, then $D_0$ is supported in $U$; (v) `hcut`: for $t$ locally of finite type, a degree-$r$ divisor $D$ and a degree-$g$ divisor $D_0$ supported in $U$ with $D.I=D_0.I\cdot(D_\gamma)_t.I$, there is an open $W\subseteq T$ through which a geometric point $s$ factors exactly when the fibre at $s$ of the rigidified twist $D.\mathrm{twistModule}$ is algebraically equivalent to zero. The conclusion: there exist a scheme $X$ and a morphism $f$ from the Yoneda presheaf of $X$ to the total presheaf over $\operatorname{Spec}R$ of the subfunctor `relSubPicPresheaf c ε (algEquivZeroCut c ε)` of the relative Picard presheaf (whose value at $t$ consists of the classes of rigidified line bundles satisfying $P$) such that the structure morphism $X\to\operatorname{Spec}R$ attached to $f$ is locally of finite type, $X$ is quasi-compact, that structure morphism factors as an open immersion $j\colon X\to Y$ followed by $y$, and for every scheme $T$ and every $T$-point $x$ of the total presheaf whose structure morphism $t$ is locally of finite type there are an open $U'\subseteq T$ and $\varphi\colon U'\to X$ with: for every rigidified line bundle $L$ whose class is the Picard component of $x$, and every field $k$ and $s\colon\operatorname{Spec}k\to T$, the range of $s$ lies in $U'$ if and only if for every two-affine cover of the fibre at $s$ the Čech $H^1$ of the fibre of $L\otimes(\mathcal O(r\varepsilon)\otimes I_{(D_\gamma)_t})$ vanishes; $\varphi$ followed by $f$ equals $U'\hookrightarrow T$ followed by $x$; and for every $\psi\colon T'\to T$ with $\psi$ followed by $t$ locally of finite type and every $\varphi'\colon T'\to X$ with $\varphi'$ followed by $f$ equal to $\psi$ followed by $x$, there is $\chi\colon T'\to U'$ with $\chi$ followed by the inclusion equal to $\psi$ and $\chi$ followed by $\varphi$ equal to $\varphi'$.
--
--   This is the construction, in Milne's style, of a single open chart for the subfunctor of the relative Picard functor of $c$ cut out by fibrewise algebraic equivalence to zero: the chart is an open subscheme of the scheme $Y$ of degree-$g$ relative divisors supported in the smooth locus $U$, and its open locus inside an arbitrary test base is characterised by the vanishing of the fibrewise Čech $H^1$ of the twisted bundle. It is used by [`AlgebraicGeometry.RelPicard.exists_openCharts_relSubPicPresheaf_algEquivZeroCut_of_relEffCartierDiv_supportedIn_of_fibrewise_zeroScheme`](thm.html#AlgebraicGeometry.RelPicard.exists_openCharts_relSubPicPresheaf_algEquivZeroCut_of_relEffCartierDiv_supportedIn_of_fibrewise_zeroScheme), which assembles such charts into a covering family on the way to representability of the relative $\mathrm{Pic}^0$ (the Jacobian) used for Néron models of the Frey curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_fibrewise_zeroScheme.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import Definitions.Def_CategoryTheory_OverTotalPresheaf
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
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

theorem AlgebraicGeometry.RelPicard.exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_fibrewise_zeroScheme
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

    (g e r : ℕ) (hr : g + e = r)

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
          (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ Dγ.idealModule))).H0 : ℤ) -
        Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ Dγ.idealModule))).H1 = 1)

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

    (havoid : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
      (L : RigidifiedLineBundle c ε t), FibrewiseAlgEquivZero L →
      ∀ (D₀ : RelEffCartierDiv c g t) (N : T.Modules), Scheme.Modules.IsInvertible N →
        Nonempty (D₀.lineBundle ≅
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)) ⊗
            (Scheme.Modules.pullback (pullback.snd c t)).obj N) →
        D₀.SupportedIn U)

    (hcut : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
      (D : RelEffCartierDiv c r t) (D₀ : RelEffCartierDiv c g t), D₀.SupportedIn U →
      D.I = D₀.I * (Dγ.pullbackAlong t (Category.comp_id t)).I →
      ∃ W : T.Opens, ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T),
        Set.range ⇑s ⊆ (W : Set T) ↔
          IsAlgEquivZero (fibreAt c t s)
            ((Scheme.Modules.pullback (pullback.fst (pullback.snd c t) s)).obj (D.twistModule c ε))) :
    ∃ (X : Scheme.{u}) (f : uliftYoneda.{u + 1}.obj X ⟶ (relSubPicPresheaf c ε (algEquivZeroCut c ε)).overTotal),
      LocallyOfFiniteType (uliftYonedaEquiv f).1 ∧ CompactSpace X ∧
      (∃ j : X ⟶ Y, IsOpenImmersion j ∧ j ≫ y = (uliftYonedaEquiv f).1) ∧
      ∀ ⦃T : Scheme.{u}⦄ (x : uliftYoneda.{u + 1}.obj T ⟶ (relSubPicPresheaf c ε (algEquivZeroCut c ε)).overTotal),
        LocallyOfFiniteType (uliftYonedaEquiv x).1 →
        ∃ (U' : T.Opens) (φ : (↑U' : Scheme.{u}) ⟶ X),
          (∀ (L : RigidifiedLineBundle c ε (uliftYonedaEquiv x).1), Quotient.mk _ L = (uliftYonedaEquiv x).2.1 →
            ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T),
              Set.range ⇑s ⊆ (U' : Set T) ↔
                ∀ (𝒲 : (pullback (pullback.snd c (uliftYonedaEquiv x).1) s).TwoAffineOpenCover),
                  Subsingleton (𝒲.sectionsOf (fibreAt c (uliftYonedaEquiv x).1 s) (fibreModule c (uliftYonedaEquiv x).1 s
                    (L.L ⊗ (sectionTwist c ε (uliftYonedaEquiv x).1 r ⊗
                      (Dγ.pullbackAlong (uliftYonedaEquiv x).1 (Category.comp_id _)).idealModule)))).H1) ∧
          uliftYoneda.{u + 1}.map φ ≫ f = uliftYoneda.{u + 1}.map U'.ι ≫ x ∧
          ∀ ⦃T' : Scheme.{u}⦄ (ψ : T' ⟶ T) (φ' : T' ⟶ X),
            LocallyOfFiniteType (ψ ≫ (uliftYonedaEquiv x).1) →
            uliftYoneda.{u + 1}.map φ' ≫ f = uliftYoneda.{u + 1}.map ψ ≫ x →
            ∃ χ : T' ⟶ ↑U', χ ≫ U'.ι = ψ ∧ χ ≫ φ = φ' := by sorry
