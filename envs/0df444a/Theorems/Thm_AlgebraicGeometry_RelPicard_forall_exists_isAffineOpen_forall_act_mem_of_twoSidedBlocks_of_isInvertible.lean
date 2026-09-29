-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_twoSidedBlocks_of_isInvertible
-- name    : AlgebraicGeometry.RelPicard.forall_exists_isAffineOpen_forall_act_mem_of_twoSidedBlocks_of_isInvertible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/5364efa0-58c1-5617-87c5-0efe3c98803f
-- title:
--   Descent orbits on relative Pic⁰ lie in affine opens
-- statement:
--   Fix a commutative ring $R$, a scheme $C$ and a separated morphism $c : C \to \operatorname{Spec} R$, together with a section $\varepsilon$ of $c$ (an element of `SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c`, i.e. a morphism $\operatorname{Spec} R \to C$ composing with $c$ to the identity). Let $R'$ be an $R$-algebra that is module-finite, étale and faithfully flat over $R$, write $\mathrm{specMap}\,R\,R' : \operatorname{Spec} R' \to \operatorname{Spec} R$ and let $C_{R'} \to \operatorname{Spec} R'$ be the base change `SmoothProperCurve.baseChange R c R'` (the second projection of $C \times_{\operatorname{Spec} R} \operatorname{Spec} R'$), with induced section $\varepsilon_{R'} =$ `SmoothProperCurve.sectionBaseChange R' ε`.
--
--   **Representing object.** $D'$ is a `RelativePic0Designation` over $R'$ for $C_{R'}$: a scheme $D'.P$ with a structure morphism $p = D'.\mathrm{toBase} : D'.P \to \operatorname{Spec} R'$ and a section $D'.\mathrm{zeroSection}$ of $p$. The datum $h'$ is a `RepresentsRelSubPic` for $(C_{R'}, \varepsilon_{R'})$ and the sub-Picard condition `algEquivZeroCut`: it consists of a rigidified line bundle (Poincaré bundle) on $C_{R'} \times_{\operatorname{Spec} R'} D'.P$ satisfying the condition `FibrewiseAlgEquivZero` (for every algebraically closed field $k$ and every $k$-point of the base, the restriction of the bundle to the corresponding fibre satisfies `IsAlgEquivZero`), the universal property that every rigidified line bundle satisfying that condition on a base $T \to \operatorname{Spec} R'$ is induced by a unique morphism $T \to D'.P$ over $\operatorname{Spec} R'$, and the triviality of the pullback of the Poincaré bundle along the zero section. Moreover $p$ is assumed locally of finite type (`hlft`).
--
--   **Open subset and block data.** $U$ is an open subset of $C$. For natural numbers $M, M'$ there are families of $R$-algebras $B_i$ ($i \in \mathrm{Fin}\,M$) and $B'_i$ ($i \in \mathrm{Fin}\,M'$) with morphisms $z_i : \operatorname{Spec} B_i \to C$ and $z'_i : \operatorname{Spec} B'_i \to C$; the hypotheses `hz`, `hz'` say that these are morphisms over $\operatorname{Spec} R$, i.e. $z_i$ followed by $c$ equals $\operatorname{Spec}$ of the structure map $R \to B_i$, and likewise for $z'_i$.
--
--   **Sections attached to the blocks.** Integers $\deg i \ge 1$ and $\deg' i \ge 1$ (hypotheses `hdeg`, `hdeg'`) index families $\sigma_{i,m}$ ($m \in \mathrm{Fin}(\deg i)$) and $\sigma'_{i,m}$ ($m \in \mathrm{Fin}(\deg' i)$) of sections of $C_{R'} \to \operatorname{Spec} R'$. The hypotheses `hσ`, `hσ'` require that each such section factors through the corresponding block: for each $i, m$ there is $y : \operatorname{Spec} R' \to \operatorname{Spec} B_i$ with $\sigma_{i,m}$ followed by the projection $C \times_{\operatorname{Spec} R}\operatorname{Spec} R' \to C$ equal to $y$ followed by $z_i$, and similarly on the primed side.
--
--   **Index set.** Natural numbers $e, \rho$ and a type $\iota$ are given, together with a map $\mathrm{idx}$ assigning to each splitting $e_1 + e_2 = e$, each injective $a : \mathrm{Fin}\,e_1 \to \mathrm{Fin}\,M$, each injective $a' : \mathrm{Fin}\,e_2 \to \mathrm{Fin}\,M'$ and each pair of choice functions $m : \prod_i \mathrm{Fin}(\deg i)$, $m' : \prod_i \mathrm{Fin}(\deg' i)$ an index in $\iota$.
--
--   **Polarising divisors.** $E$ is a relative effective Cartier divisor of degree $\rho$ for $c$ over the identity of $\operatorname{Spec} R$, and $E'$ one of degree $\rho$ for $C_{R'}$ over the identity of $\operatorname{Spec} R'$ (in each case an ideal sheaf datum whose closed subscheme is finite, flat and locally of finite presentation over the base with fibre rank $\rho$ everywhere); $\mathcal{O}(E)$ and $\mathcal{O}(E')$ denote the associated `lineBundle`, the dual of the ideal module. The hypothesis `hEE'` compares them on geometric fibres: for every algebraically closed field $\Omega$, every $s_\Omega : \operatorname{Spec}\Omega \to \operatorname{Spec} R'$ and every isomorphism $\varphi$ between $C_{R'} \times_{\operatorname{Spec} R'} \operatorname{Spec}\Omega$ and $C \times_{\operatorname{Spec} R} \operatorname{Spec}\Omega$ that is compatible with the two projections to $C$, the pullback along $\varphi$ of $\mathcal{O}(E)$ restricted along $s_\Omega$ followed by $\mathrm{specMap}\,R\,R'$ is isomorphic to $\mathcal{O}(E')$ restricted along $s_\Omega$.
--
--   **Charts.** $X : \iota \to \mathbf{Sch}$ is a family of schemes with morphisms $f_i$ from the (lifted) Yoneda presheaf of $X_i$ to `(relSubPicPresheaf C_{R'} ε_{R'} (algEquivZeroCut …)).overTotal`, the presheaf on schemes whose $T$-points are pairs consisting of a structure morphism $T \to \operatorname{Spec} R'$ and an element of the $\mathrm{Pic}^0$-cut presheaf over it. The hypothesis `hf` requires each $f_i$ to be an open immersion in the relative sense `MorphismProperty.presheafULift @IsOpenImmersion`, and `hfin` requires that every finite subset of $X_i$ is contained in some affine open of $X_i$.
--
--   **Chart divisors.** $D_\gamma$ assigns to each $\gamma \in \iota$ a relative effective Cartier divisor of degree $e$ for $C_{R'}$ over the identity of $\operatorname{Spec} R'$. The hypothesis `hDγ` identifies its ideal at the indices in the image of $\mathrm{idx}$: for every splitting $e_1+e_2=e$, injective $a, a'$ and choices $m, m'$, the ideal of $D_\gamma(\mathrm{idx}\,e_1\,e_2\,\cdot\,a\,a'\,m\,m')$ is the product of `prodKerGraph` of the sections $\sigma_{a(j),\,m(a(j))}$ ($j \in \mathrm{Fin}\,e_1$) and `prodKerGraph` of the sections $\sigma'_{a'(j),\,m'(a'(j))}$ ($j \in \mathrm{Fin}\,e_2$), where `prodKerGraph` is the product over $j$ of the kernel ideals of the graph morphisms of the given sections.
--
--   **Invertibility and base-change hypotheses.** `hεinv`: for every scheme $T$ and every $t : T \to \operatorname{Spec} R'$, the ideal `sectionIdeal` of the rigidifying section of $C_{R'}$ over $t$ is invertible in the sense of `IsInvertible` (locally generated by one non-zero-divisor on affine basic opens). `hTw`: for all $t : T \to \operatorname{Spec} R'$, $t' : T' \to \operatorname{Spec} R'$ and every morphism $\psi$ from $t'$ to $t$ over $\operatorname{Spec} R'$, the pullback of $\mathcal{O}(E'_t)$ along `baseChangeSnd` of $\psi$ is isomorphic to $\mathcal{O}(E'_{t'})$. `hEinv` and `hDγinv`: for every $t : T \to \operatorname{Spec} R'$ the ideals of $E'$ pulled back along $t$, respectively of $D_\gamma(\gamma)$ pulled back along $t$ for each $\gamma \in \iota$, are invertible.
--
--   **Per-chart membership criterion `hmem`.** For each $\gamma \in \iota$, each scheme $T$ and each $T$-point $x$ of the total presheaf, write $t$ for its structure component $T \to \operatorname{Spec} R'$ and assume $t$ is locally of finite type; let $L$ be any rigidified line bundle for $(C_{R'}, \varepsilon_{R'})$ over $t$ whose class equals the second component of $x$. Then for every field $k$ and every $s : \operatorname{Spec} k \to T$ satisfying the two conditions
--   (i) for every `TwoAffineOpenCover` $\mathcal{W}$ of the fibre $(C_{R'}\times_{\operatorname{Spec} R'} T)\times_T \operatorname{Spec} k$, the group $H^1$ of the two-chart Čech complex `𝒲.sectionsOf` of the fibre restriction of $L.L \otimes (\mathcal{O}(E'_t) \otimes I_{D_\gamma(\gamma),t})$ is a subsingleton, where $I$ denotes the ideal module `idealModule`, and
--   (ii) every morphism $\tau$ from the unit module to the pullback along `mapOnProdOver` of $L.L \otimes (\mathcal{O}(E'_t) \otimes I_{D_\gamma(\gamma),t})$ over $s$ followed by $t$ which is non-zero has the support of its zero scheme ideal `zeroSchemeIdeal` contained in the preimage of the preimage of $U$ under the projections to $C_{R'}$ and then to $C$,
--   there exists $\varphi' : \operatorname{Spec} k \to X_\gamma$ with $\varphi'$ followed by $f_\gamma$ equal to $s$ followed by $x$ (after applying the lifted Yoneda embedding).
--
--   **General-position hypothesis `hgp`.** For every algebraically closed field $\Omega$ that is an $R$-algebra and every module $L_0$ on $C \times_{\operatorname{Spec} R}\operatorname{Spec}\Omega$ which is invertible and satisfies `IsAlgEquivZero` relative to the second projection, there are $e_1, e_2$ with $e_1 + e_2 = e$ and injective maps $a : \mathrm{Fin}\,e_1 \to \mathrm{Fin}\,M$, $a' : \mathrm{Fin}\,e_2 \to \mathrm{Fin}\,M'$ such that the following holds for all families $v$ (indexed by $\mathrm{Fin}\,e_1$) and $v'$ (indexed by $\mathrm{Fin}\,e_2$) of $\Omega$-points of the fibre that are sections of its structure morphism: if each $v_j$ factors through $z_{a(j)}$ via some $R$-algebra homomorphism $B_{a(j)} \to \Omega$, and each $v'_j$ factors through $z'_{a'(j)}$ via some $R$-algebra homomorphism $B'_{a'(j)} \to \Omega$, then (i) for every `TwoAffineOpenCover` of the fibre the group $H^1$ of the two-chart Čech complex of $L_0 \otimes (\mathcal{O}(E_\Omega) \otimes ((\prod_j \ker v_j)(\prod_j \ker v'_j))\text{-module})$ is a subsingleton, and (ii) every non-zero morphism $\tau$ from the unit module to that same tensor product has the support of `zeroSchemeIdeal τ` contained in the preimage of $U$ under the projection to $C$.
--
--   **Conclusion.** Under these hypotheses, for every point $x$ of $D'.P$ there exists an open subset $W$ of $D'.P$ such that $W$ is an affine open, and such that for every point $r$ of the pullback of $p$ followed by $\mathrm{specMap}\,R\,R'$ along $\mathrm{specMap}\,R\,R'$ whose image under the first projection is $x$, the image of $r$ under the action morphism of the descent action `DescentAction.ofRepresentableBy` for $\mathrm{specMap}\,R\,R'$, the presheaf `relSubPicPresheaf c ε (algEquivZeroCut c ε)` and $p$, obtained from the representability datum [`AlgebraicGeometry.RelPicard.BaseChange.representableByRestrict c ε R' h'`](def/AlgebraicGeometry_RelSubPicBaseChange.html#L271), belongs to $W$.
--
--   This is the chart-covering step in the construction of a representing object for the $\mathrm{Pic}^0$ cut of a pointed curve over $\operatorname{Spec} R$ by descent from a finite étale cover $\operatorname{Spec} R'$: it asserts that the whole orbit, under the canonical descent action, of the fibre above a given point of the representing scheme over $R'$ can be caught inside a single affine open. It is used by [`AlgebraicGeometry.RelPicard.forall_prime_exists_representsRelSubPic_algEquivZeroCut_baseChange_away_of_smoothLocus_of_twoGluedSmoothCurveDegenerations`](thm.html#AlgebraicGeometry.RelPicard.forall_prime_exists_representsRelSubPic_algEquivZeroCut_baseChange_away_of_smoothLocus_of_twoGluedSmoothCurveDegenerations), where the charts are indexed by splittings and injective tuples drawn from two families of blocks, as is appropriate for curves degenerating to two smooth curves meeting transversally.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_twoSidedBlocks_of_isInvertible.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import Definitions.Def_CategoryTheory_OverTotalPresheaf
import Definitions.Def_AlgebraicGeometry_LocalRepresentabilityULift
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_DescentAction
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian

theorem AlgebraicGeometry.RelPicard.forall_exists_isAffineOpen_forall_act_mem_of_twoSidedBlocks_of_isInvertible
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (R' : Type u) [CommRing R'] [Algebra R R'] [Module.Finite R R'] [Algebra.Etale R R']
    [Module.FaithfullyFlat R R']
    (D' : RelativePic0Designation R' (SmoothProperCurve.baseChange R c R'))
    (h' : RepresentsRelSubPic (SmoothProperCurve.baseChange R c R') (SmoothProperCurve.sectionBaseChange R' ε)
      (algEquivZeroCut (SmoothProperCurve.baseChange R c R') (SmoothProperCurve.sectionBaseChange R' ε)) D')
    (hlft : LocallyOfFiniteType D'.toBase)

    (U : C.Opens)

    {M M' : ℕ} (B : Fin M → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    (B' : Fin M' → Type u) [∀ i, CommRing (B' i)] [∀ i, Algebra R (B' i)]
    (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ C) (z' : ∀ i, Spec (CommRingCat.of (B' i)) ⟶ C)
    (hz : ∀ i, z i ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R (B i))))
    (hz' : ∀ i, z' i ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R (B' i))))

    (deg : Fin M → ℕ) (hdeg : ∀ i, 1 ≤ deg i) (deg' : Fin M' → ℕ) (hdeg' : ∀ i, 1 ≤ deg' i)
    (σ : ∀ i, Fin (deg i) → SchemeHomOver (𝟙 (Spec (CommRingCat.of R'))) (SmoothProperCurve.baseChange R c R'))
    (σ' : ∀ i, Fin (deg' i) → SchemeHomOver (𝟙 (Spec (CommRingCat.of R'))) (SmoothProperCurve.baseChange R c R'))
    (hσ : ∀ i m, ∃ y : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of (B i)),
      (σ i m).1 ≫ pullback.fst c (SmoothProperCurve.specMap R R') = y ≫ z i)
    (hσ' : ∀ i m, ∃ y : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of (B' i)),
      (σ' i m).1 ≫ pullback.fst c (SmoothProperCurve.specMap R R') = y ≫ z' i)

    (e ρ : ℕ) {ι : Type u}
    (idx : ∀ (e₁ e₂ : ℕ), e₁ + e₂ = e → {a : Fin e₁ → Fin M // Function.Injective a} →
      {a' : Fin e₂ → Fin M' // Function.Injective a'} → (∀ i, Fin (deg i)) → (∀ i, Fin (deg' i)) → ι)

    (E : RelEffCartierDiv c ρ (𝟙 (Spec (CommRingCat.of R))))
    (E' : RelEffCartierDiv (SmoothProperCurve.baseChange R c R') ρ (𝟙 (Spec (CommRingCat.of R'))))
    (hEE' : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (sΩ : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R'))
      (φ : pullback (SmoothProperCurve.baseChange R c R') sΩ ≅ pullback c (sΩ ≫ SmoothProperCurve.specMap R R')),
      φ.hom ≫ pullback.fst c (sΩ ≫ SmoothProperCurve.specMap R R') =
        pullback.fst (SmoothProperCurve.baseChange R c R') sΩ ≫ pullback.fst c (SmoothProperCurve.specMap R R') →
      Nonempty ((Scheme.Modules.pullback φ.hom).obj
          (E.pullbackAlong (sΩ ≫ SmoothProperCurve.specMap R R') (Category.comp_id _)).lineBundle ≅
        (E'.pullbackAlong sΩ (Category.comp_id sΩ)).lineBundle))
    (X : ι → Scheme.{u})
    (f : ∀ i, uliftYoneda.{u + 1}.obj (X i) ⟶
      (relSubPicPresheaf (SmoothProperCurve.baseChange R c R') (SmoothProperCurve.sectionBaseChange R' ε)
        (algEquivZeroCut (SmoothProperCurve.baseChange R c R') (SmoothProperCurve.sectionBaseChange R' ε))).overTotal)
    (hf : ∀ i, MorphismProperty.presheafULift.{u + 1} @IsOpenImmersion (f i))
    (hfin : ∀ (i : ι) (F : Finset (X i)), ∃ U : (X i).Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U)
    (Dγ : ι → RelEffCartierDiv (SmoothProperCurve.baseChange R c R') e (𝟙 (Spec (CommRingCat.of R'))))
    (hDγ : ∀ (e₁ e₂ : ℕ) (he : e₁ + e₂ = e) (a : {a : Fin e₁ → Fin M // Function.Injective a})
      (a' : {a' : Fin e₂ → Fin M' // Function.Injective a'}) (m : ∀ i, Fin (deg i)) (m' : ∀ i, Fin (deg' i)),
      (Dγ (idx e₁ e₂ he a a' m m')).I =
        prodKerGraph (SmoothProperCurve.baseChange R c R')
          (fun j => (σ (a.1 j) (m (a.1 j))).1) (fun j => (σ (a.1 j) (m (a.1 j))).2) *
        prodKerGraph (SmoothProperCurve.baseChange R c R')
          (fun j => (σ' (a'.1 j) (m' (a'.1 j))).1) (fun j => (σ' (a'.1 j) (m' (a'.1 j))).2))

    (hεinv : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R')),
      (sectionIdeal (SmoothProperCurve.baseChange R c R') (SmoothProperCurve.sectionBaseChange R' ε) t).IsInvertible)
    (hTw : ∀ ⦃T T' : Scheme.{u}⦄ {t : T ⟶ Spec (CommRingCat.of R')} {t' : T' ⟶ Spec (CommRingCat.of R')}
      (ψ : SchemeHomOver t' t),
      Nonempty ((Scheme.Modules.pullback (baseChangeSnd (SmoothProperCurve.baseChange R c R') ψ)).obj
        (E'.pullbackAlong t (Category.comp_id t)).lineBundle ≅ (E'.pullbackAlong t' (Category.comp_id t')).lineBundle))
    (hEinv : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R')),
      ((E'.pullbackAlong t (Category.comp_id t)).I).IsInvertible)
    (hDγinv : ∀ (i : ι) ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R')),
      ((Dγ i).pullbackAlong t (Category.comp_id t)).I.IsInvertible)

    (hmem : ∀ (i : ι) ⦃T : Scheme.{u}⦄
      (x : uliftYoneda.{u + 1}.obj T ⟶
        (relSubPicPresheaf (SmoothProperCurve.baseChange R c R') (SmoothProperCurve.sectionBaseChange R' ε)
          (algEquivZeroCut (SmoothProperCurve.baseChange R c R') (SmoothProperCurve.sectionBaseChange R' ε))).overTotal),
      LocallyOfFiniteType (uliftYonedaEquiv x).1 →
      ∀ (L : RigidifiedLineBundle (SmoothProperCurve.baseChange R c R') (SmoothProperCurve.sectionBaseChange R' ε)
        (uliftYonedaEquiv x).1), Quotient.mk _ L = (uliftYonedaEquiv x).2.1 →
      ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T),
        (∀ (𝒲 : (pullback (pullback.snd (SmoothProperCurve.baseChange R c R') (uliftYonedaEquiv x).1) s).TwoAffineOpenCover),
          Subsingleton (𝒲.sectionsOf (fibreAt (SmoothProperCurve.baseChange R c R') (uliftYonedaEquiv x).1 s)
            (fibreModule (SmoothProperCurve.baseChange R c R') (uliftYonedaEquiv x).1 s
            (L.L ⊗ ((E'.pullbackAlong (uliftYonedaEquiv x).1 (Category.comp_id _)).lineBundle ⊗
              ((Dγ i).pullbackAlong (uliftYonedaEquiv x).1 (Category.comp_id _)).idealModule)))).H1) →

        (∀ τ : 𝟙_ (pullback (SmoothProperCurve.baseChange R c R') (s ≫ (uliftYonedaEquiv x).1)).Modules ⟶
            (Scheme.Modules.pullback (mapOnProdOver (SmoothProperCurve.baseChange R c R') s rfl)).obj
              (L.L ⊗ ((E'.pullbackAlong (uliftYonedaEquiv x).1 (Category.comp_id _)).lineBundle ⊗
                ((Dγ i).pullbackAlong (uliftYonedaEquiv x).1 (Category.comp_id _)).idealModule)),
          τ ≠ 0 → ((Scheme.Modules.zeroSchemeIdeal τ).support :
              Set ↥(pullback (SmoothProperCurve.baseChange R c R') (s ≫ (uliftYonedaEquiv x).1))) ⊆
            ((pullback.fst (SmoothProperCurve.baseChange R c R') (s ≫ (uliftYonedaEquiv x).1)) ⁻¹ᵁ
                (pullback.fst c (SmoothProperCurve.specMap R R') ⁻¹ᵁ U) :
              Set ↥(pullback (SmoothProperCurve.baseChange R c R') (s ≫ (uliftYonedaEquiv x).1)))) →
        ∃ φ' : Spec (CommRingCat.of k) ⟶ X i,
          uliftYoneda.{u + 1}.map φ' ≫ f i = uliftYoneda.{u + 1}.map s ≫ x)

    (hgp : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra R Ω]
      (L₀ : (pullback c (SmoothProperCurve.specMap R Ω)).Modules), Scheme.Modules.IsInvertible L₀ →
      IsAlgEquivZero (pullback.snd c (SmoothProperCurve.specMap R Ω)) L₀ →
      ∃ (e₁ e₂ : ℕ) (_ : e₁ + e₂ = e) (a : Fin e₁ → Fin M) (a' : Fin e₂ → Fin M'),
        Function.Injective a ∧ Function.Injective a' ∧
        ∀ (v : Fin e₁ → {q : Spec (CommRingCat.of Ω) ⟶ pullback c (SmoothProperCurve.specMap R Ω) //
            q ≫ pullback.snd c (SmoothProperCurve.specMap R Ω) = 𝟙 _})
          (v' : Fin e₂ → {q : Spec (CommRingCat.of Ω) ⟶ pullback c (SmoothProperCurve.specMap R Ω) //
            q ≫ pullback.snd c (SmoothProperCurve.specMap R Ω) = 𝟙 _}),
          (∀ j, ∃ ψ : B (a j) →ₐ[R] Ω,
            (v j).1 ≫ pullback.fst c (SmoothProperCurve.specMap R Ω) =
              Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ z (a j)) →
          (∀ j, ∃ ψ : B' (a' j) →ₐ[R] Ω,
            (v' j).1 ≫ pullback.fst c (SmoothProperCurve.specMap R Ω) =
              Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ z' (a' j)) →
          (∀ 𝒲 : (pullback c (SmoothProperCurve.specMap R Ω)).TwoAffineOpenCover,
            Subsingleton (𝒲.sectionsOf (pullback.snd c (SmoothProperCurve.specMap R Ω))
              (L₀ ⊗ ((E.pullbackAlong (SmoothProperCurve.specMap R Ω) (Category.comp_id _)).lineBundle ⊗
                ((∏ j, (v j).1.ker) * (∏ j, (v' j).1.ker)).module))).H1) ∧
          (∀ τ : 𝟙_ (pullback c (SmoothProperCurve.specMap R Ω)).Modules ⟶
              (L₀ ⊗ ((E.pullbackAlong (SmoothProperCurve.specMap R Ω) (Category.comp_id _)).lineBundle ⊗
                ((∏ j, (v j).1.ker) * (∏ j, (v' j).1.ker)).module)),
            τ ≠ 0 → ((Scheme.Modules.zeroSchemeIdeal τ).support : Set ↥(pullback c (SmoothProperCurve.specMap R Ω))) ⊆
              ((pullback.fst c (SmoothProperCurve.specMap R Ω)) ⁻¹ᵁ U : Set ↥(pullback c (SmoothProperCurve.specMap R Ω))))) :
    ∀ x : D'.P, ∃ W : D'.P.Opens, IsAffineOpen W ∧
      ∀ r : ↑(pullback (D'.toBase ≫ SmoothProperCurve.specMap R R') (SmoothProperCurve.specMap R R')),
        (pullback.fst (D'.toBase ≫ SmoothProperCurve.specMap R R') (SmoothProperCurve.specMap R R')) r = x →
        (DescentAction.ofRepresentableBy (SmoothProperCurve.specMap R R')
          (relSubPicPresheaf c ε (algEquivZeroCut c ε)) D'.toBase
          (AlgebraicGeometry.RelPicard.BaseChange.representableByRestrict c ε R' h')).act r ∈ W := by sorry
