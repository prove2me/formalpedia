-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_representsRelSubPic_algEquivZeroCut_of_smoothLocus_of_twoGluedSmoothCurveDegenerations
-- name    : AlgebraicGeometry.RelPicard.exists_representsRelSubPic_algEquivZeroCut_of_smoothLocus_of_twoGluedSmoothCurveDegenerations
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/bd0b35f4-ccf7-5c6b-8bf5-70faf1463d5f
-- title:
--   Relative Pic⁰ for curves degenerating to two glued smooth curves
-- statement:
--   Let $R$ be a reduced Noetherian commutative ring, let $C$ be a scheme and let $c \colon C \to \operatorname{Spec} R$ be proper and flat. Let $\mathcal V$ be a `Scheme.TwoAffineOpenCover` of $C$, that is, a pair of opens $U_0, U_1$ of $C$, both affine, with $U_0 \sqcup U_1 = \top$ and with $U_0 \cap U_1$ affine. Let $g, d_0 \in \mathbb N$.
--
--   **Global sections (`hH0`).** For every $R$-algebra $A$, the structure map $A \to \Gamma(C \times_{\operatorname{Spec} R} \operatorname{Spec} A, \top)$, taken for the $A$-algebra structure induced by the second projection, is bijective.
--
--   **The smooth locus (`hUmax`, `hcov`).** $U$ is an open of $C$ such that $U \hookrightarrow C \to \operatorname{Spec} R$ is smooth of relative dimension $1$, and $U$ is maximal with this property: every open $W$ of $C$ for which $W \hookrightarrow C \to \operatorname{Spec} R$ is smooth of relative dimension $1$ satisfies $W \le U$. Furthermore, for every affine open $V$ of $\operatorname{Spec} R$ and every finite set $F$ of points of $U$ whose images in $\operatorname{Spec} R$ lie in $V$, there is an affine open $W$ of the scheme $U$ contained in the preimage of $V$ and containing every point of $F$.
--
--   **The section (`hε`).** $\varepsilon$ is a section of $c$, i.e. a morphism $\operatorname{Spec} R \to C$ with $\varepsilon \circ$-composite $c$ equal to the identity, whose set-theoretic image is contained in $U$.
--
--   Throughout, a line bundle $L$ on a $k$-scheme $a \colon A \to \operatorname{Spec} k$ is *algebraically equivalent to zero* (`IsAlgEquivZero`) when there exist a locally of finite type, geometrically integral $h \colon T' \to \operatorname{Spec} k$, an invertible module $M$ on $A \times_k T'$ and two sections $t_0, t_1$ of $h$ such that the pullback of $M$ along the base change at $t_0$ is isomorphic to the structure sheaf and the pullback of $M$ along the base change at $t_1$ is isomorphic to the pullback of $L$.
--
--   **Geometric fibres (`hfib`, `hgred`, `hg`).** For every algebraically closed field $k$ and every $x \colon \operatorname{Spec} k \to \operatorname{Spec} R$: every invertible module $L$ on the fibre $C \times_{\operatorname{Spec} R} \operatorname{Spec} k$ which is algebraically equivalent to zero and admits a nonzero morphism from the unit module is isomorphic to the unit module (`hfib`); the fibre is reduced (`hgred`); and for every two-affine open cover $\mathcal W$ of the fibre of $\mathrm{pr}_2 \colon C \times_{\operatorname{Spec} R} \operatorname{Spec} R \to \operatorname{Spec} R$ at $x$, the $k$-dimension of the Čech group $H^1$ of the sections of the structure sheaf with respect to $\mathcal W$ — the quotient of $\Gamma(\mathcal W_0 \cap \mathcal W_1)$ by the image of the Čech differential on $\Gamma(\mathcal W_0) \oplus \Gamma(\mathcal W_1)$ — equals $g$ (`hg`).
--
--   **Pools of split blocks on both sides (`hpool`).** For every prime $\mathfrak p$ of $R$ and all $A_0, B_0, n_0 \in \mathbb N$ there exist $f \notin \mathfrak p$, bounds $b, M, M' \in \mathbb N$ with $A_0 b^{n_0} + B_0 < M$ and $A_0 b^{n_0} + B_0 < M'$, a ring $R'$ that is an $R$-algebra and an algebra over $R_f = \mathrm{Localization.Away}\, f$ compatibly, module-finite, étale and faithfully flat over $R_f$, together with two families of blocks: $R_f$-algebras $B_i$ ($i \in \mathrm{Fin}\, M$), each module-finite and étale over $R_f$, degrees $\deg i$ with $1 \le \deg i \le b$, $R'$-algebra isomorphisms $R' \otimes_{R_f} B_i \cong R'^{\deg i}$, and closed immersions $z_i \colon \operatorname{Spec} B_i \to C \times_{\operatorname{Spec} R} \operatorname{Spec} R_f$; and likewise $R_f$-algebras $B'_i$ ($i \in \mathrm{Fin}\, M'$) with the same finiteness, étaleness, degree bounds $1 \le \deg' i \le b$, splittings over $R'$ and closed immersions $z'_i$. These data satisfy: each $z_i$ is a morphism over $\operatorname{Spec} R_f$, i.e. its composite with the projection to $\operatorname{Spec} R_f$ is the canonical map $\operatorname{Spec} B_i \to \operatorname{Spec} R_f$; the image of each $z_i$ lies in the preimage of $U$ under the first projection; the images of the $z_i$ are pairwise disjoint; for every algebraically closed field $k$, every $s \colon \operatorname{Spec} k \to \operatorname{Spec} R_f$ and every $i$, the preimage in the fibre at $s$ of the image of $z_i$ is contained in the connected component, inside the preimage of $U$ in that fibre, of the point obtained by evaluating the base-changed section $\varepsilon$ at the closed point of $\operatorname{Spec} k$; some $j$ has $\deg' j \le d_0$; each $z'_i$ is a morphism over $\operatorname{Spec} R_f$; the image of each $z'_i$ lies in the preimage of $U$; the images of the $z'_i$ are pairwise disjoint; the image of each $z_i$ is disjoint from the image of each $z'_j$; and for every algebraically closed field $k$, every $s \colon \operatorname{Spec} k \to \operatorname{Spec} R_f$ and every $i$, if the fibre at $s$ is not smooth then the preimage in that fibre of the image of $z'_i$ is contained in the preimage of $U$ with the connected component of the $\varepsilon$-point removed.
--
--   **Shape of the degenerate geometric fibres (`hbad`).** For every algebraically closed field $k$ and every $s \colon \operatorname{Spec} k \to \operatorname{Spec} R$ such that the fibre $X = C \times_{\operatorname{Spec} R} \operatorname{Spec} k$ is not smooth over $\operatorname{Spec} k$, there exist schemes $C_1, C_2$ with structure morphisms $c_1, c_2$ to $\operatorname{Spec} k$ which are proper, smooth of relative dimension $1$ and geometrically integral, closed immersions $i_1 \colon C_1 \to X$ and $i_2 \colon C_2 \to X$ over $\operatorname{Spec} k$, and $n \in \mathbb N$, such that: every point of $X$ lies in the image of $i_1$ or in the image of $i_2$; the scheme $C_1 \times_X C_2$ is reduced, its underlying set has exactly $n$ elements, and $n > 0$; the point of $X$ determined by $\varepsilon$ and the closed point of $\operatorname{Spec} k$ lies in the image of $i_1$ but not in that of $i_2$; the preimage of $U$ in $X$ is the complement of the image of $C_1 \times_X C_2 \to C_1 \to X$; the intersection of the image of $i_1$ with the preimage of $U$ is the connected component of the $\varepsilon$-point in the preimage of $U$, while the intersection of the image of $i_2$ with the preimage of $U$ is the complement of that connected component inside the preimage of $U$; and there are opens $W_1, W_2$ of $X$ whose underlying sets are the complements of the images of $i_2$ and of $i_1$ respectively, such that the inclusion of $i_1^{-1}W_1$ followed by $i_1$, and the inclusion of $i_2^{-1}W_2$ followed by $i_2$, are open immersions.
--
--   **Conclusion.** There exists a `RelativePic0Designation` $D$ for $c$, that is, a scheme $D.P$ with a morphism $D.\mathrm{toBase} \colon D.P \to \operatorname{Spec} R$ and a section $D.\mathrm{zeroSection}$ of it, such that:
--
--   1. `RepresentsRelSubPic c ε (algEquivZeroCut c ε) D` is nonempty: there is a rigidified line bundle (an invertible module on $C \times_{\operatorname{Spec} R} D.P$ together with a trivialisation of its restriction along the rigidifying section determined by $\varepsilon$) which is fibrewise algebraically equivalent to zero — for every algebraically closed field $k$ and every $k$-point of $D.P$, its pullback to the corresponding fibre of $C$ is algebraically equivalent to zero in the above sense — which is universal, in that for every $t \colon T \to \operatorname{Spec} R$ and every rigidified line bundle $M$ on $C \times_{\operatorname{Spec} R} T$ that is fibrewise algebraically equivalent to zero there is a unique morphism $T \to D.P$ over $\operatorname{Spec} R$ whose pullback of the Poincaré bundle has underlying module isomorphic to that of $M$, and whose pullback along $D.\mathrm{zeroSection}$ has underlying module isomorphic to the structure sheaf;
--
--   2. $D.\mathrm{toBase}$ is smooth;
--
--   3. $D.\mathrm{toBase}$ is separated;
--
--   4. $D.\mathrm{toBase}$ is quasi-compact;
--
--   5. $D.\mathrm{toBase}$ is surjective;
--
--   6. $D.\mathrm{toBase}$ is geometrically connected.
--
--   This is the existence of a relative $\mathrm{Pic}^0$ (a Jacobian scheme, smooth with connected fibres over the base) for a proper flat pointed curve over a reduced Noetherian base whose non-smooth geometric fibres are unions of two smooth proper geometrically integral curves meeting in a finite nonempty reduced set of points, with the section lying on the first component. It is the general-genus degeneration input used by the constructions of Jacobians of modular curves over their integral models, being cited by [`ModularCurve.DRModelPackageLevel.exists_representsRelSubPic`](thm.html#ModularCurve.DRModelPackageLevel.exists_representsRelSubPic), [`ModularCurve.XHDRModelAtP.exists_representsRelSubPic_algEquivZeroCut_epsInf_of_atkinLehner_generic_of_ker_le`](thm.html#ModularCurve.XHDRModelAtP.exists_representsRelSubPic_algEquivZeroCut_epsInf_of_atkinLehner_generic_of_ker_le) and [`ModularCurve.XOneP.exists_representsRelSubPic_algEquivZeroCut_twoChartModel_x1_mul`](thm.html#ModularCurve.XOneP.exists_representsRelSubPic_algEquivZeroCut_twoChartModel_x1_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_representsRelSubPic_algEquivZeroCut_of_smoothLocus_of_twoGluedSmoothCurveDegenerations.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian

theorem AlgebraicGeometry.RelPicard.exists_representsRelSubPic_algEquivZeroCut_of_smoothLocus_of_twoGluedSmoothCurveDegenerations
    (R : Type u) [CommRing R] [IsNoetherianRing R] [_root_.IsReduced R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c] [Flat c]
    (𝒱 : C.TwoAffineOpenCover)
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))

    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (hUmax : ∀ W : C.Opens, SmoothOfRelativeDimension 1 (W.ι ≫ c) → W ≤ U)
    (hcov : ∀ (V : (Spec (CommRingCat.of R)).affineOpens) (F : Finset ↥U),
      (∀ x ∈ F, (U.ι ≫ c).base x ∈ (V : (Spec (CommRingCat.of R)).Opens)) →
      ∃ W : (U : Scheme.{u}).Opens, IsAffineOpen W ∧
        W ≤ (U.ι ≫ c) ⁻¹ᵁ (V : (Spec (CommRingCat.of R)).Opens) ∧ ∀ x ∈ F, x ∈ W)

    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (hε : Set.range ε.1.base ⊆ (U : Set C))

    (hfib : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (L : (pullback c x).Modules), Scheme.Modules.IsInvertible L →
      IsAlgEquivZero (pullback.snd c x) L →
      ∀ s : 𝟙_ (pullback c x).Modules ⟶ L, s ≠ 0 → Nonempty (L ≅ 𝟙_ (pullback c x).Modules))

    (hgred : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)), IsReduced (pullback c x))
    (g : ℕ)
    (hg : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover),
      Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
        (SheafOfModules.unit (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).ringCatSheaf)).H1 = g)

    (d₀ : ℕ)
    (hpool : ∀ (𝔭 : PrimeSpectrum R) (A₀ B₀ n₀ : ℕ), ∃ (f : R) (_ : f ∉ 𝔭.asIdeal) (b M M' : ℕ)
      (_ : A₀ * b ^ n₀ + B₀ < M) (_ : A₀ * b ^ n₀ + B₀ < M')
      (R' : Type u) (_ : CommRing R') (_ : Algebra R R')
      (_ : Algebra (Localization.Away f) R') (_ : IsScalarTower R (Localization.Away f) R')
      (_ : Module.Finite (Localization.Away f) R') (_ : Algebra.Etale (Localization.Away f) R')
      (_ : Module.FaithfullyFlat (Localization.Away f) R')
      (B : Fin M → Type u) (_ : ∀ i, CommRing (B i)) (_ : ∀ i, Algebra (Localization.Away f) (B i))
      (_ : ∀ i, Module.Finite (Localization.Away f) (B i)) (_ : ∀ i, Algebra.Etale (Localization.Away f) (B i))
      (deg : Fin M → ℕ) (_ : ∀ i, 1 ≤ deg i) (_ : ∀ i, deg i ≤ b)
      (φ : ∀ i, TensorProduct (Localization.Away f) R' (B i) ≃ₐ[R'] (Fin (deg i) → R'))
      (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ pullback c (specMap R (Localization.Away f)))
      (_ : ∀ i, IsClosedImmersion (z i))
      (B' : Fin M' → Type u) (_ : ∀ i, CommRing (B' i)) (_ : ∀ i, Algebra (Localization.Away f) (B' i))
      (_ : ∀ i, Module.Finite (Localization.Away f) (B' i)) (_ : ∀ i, Algebra.Etale (Localization.Away f) (B' i))
      (deg' : Fin M' → ℕ) (_ : ∀ i, 1 ≤ deg' i) (_ : ∀ i, deg' i ≤ b)
      (φ' : ∀ i, TensorProduct (Localization.Away f) R' (B' i) ≃ₐ[R'] (Fin (deg' i) → R'))
      (z' : ∀ i, Spec (CommRingCat.of (B' i)) ⟶ pullback c (specMap R (Localization.Away f)))
      (_ : ∀ i, IsClosedImmersion (z' i)),

      (∀ i, z i ≫ baseChange R c (Localization.Away f) = specMap (Localization.Away f) (B i)) ∧
      (∀ i, Set.range (z i).base ⊆
        ((pullback.fst c (specMap R (Localization.Away f)) ⁻¹ᵁ U : (pullback c (specMap R (Localization.Away f))).Opens) :
          Set ↥(pullback c (specMap R (Localization.Away f))))) ∧
      (Pairwise fun i j => Disjoint (Set.range (z i).base) (Set.range (z j).base)) ∧
      (∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f)))
        (i : Fin M),
        (pullback.fst (baseChange R c (Localization.Away f)) s).base ⁻¹' Set.range (z i).base ⊆
          connectedComponentIn
            (((pullback.fst (baseChange R c (Localization.Away f)) s ≫ pullback.fst c (specMap R (Localization.Away f))) ⁻¹ᵁ U :
                (pullback (baseChange R c (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange R c (Localization.Away f)) s))
            (((sectionFibrePoint (sectionBaseChange (Localization.Away f) ε) s).1).base (IsLocalRing.closedPoint k))) ∧

      (∃ j, deg' j ≤ d₀) ∧
      (∀ i, z' i ≫ baseChange R c (Localization.Away f) = specMap (Localization.Away f) (B' i)) ∧
      (∀ i, Set.range (z' i).base ⊆
        ((pullback.fst c (specMap R (Localization.Away f)) ⁻¹ᵁ U : (pullback c (specMap R (Localization.Away f))).Opens) :
          Set ↥(pullback c (specMap R (Localization.Away f))))) ∧
      (Pairwise fun i j => Disjoint (Set.range (z' i).base) (Set.range (z' j).base)) ∧
      (∀ i j, Disjoint (Set.range (z i).base) (Set.range (z' j).base)) ∧
      (∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f)))
        (i : Fin M'), ¬ Smooth (pullback.snd (baseChange R c (Localization.Away f)) s) →
        (pullback.fst (baseChange R c (Localization.Away f)) s).base ⁻¹' Set.range (z' i).base ⊆
          (((pullback.fst (baseChange R c (Localization.Away f)) s ≫ pullback.fst c (specMap R (Localization.Away f))) ⁻¹ᵁ U :
                (pullback (baseChange R c (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange R c (Localization.Away f)) s)) \
          connectedComponentIn
            (((pullback.fst (baseChange R c (Localization.Away f)) s ≫ pullback.fst c (specMap R (Localization.Away f))) ⁻¹ᵁ U :
                (pullback (baseChange R c (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange R c (Localization.Away f)) s))
            (((sectionFibrePoint (sectionBaseChange (Localization.Away f) ε) s).1).base (IsLocalRing.closedPoint k))))

    (hbad : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)), ¬ Smooth (pullback.snd c s) →
      ∃ (C₁ C₂ : Scheme.{u}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
        (_ : IsProper c₁) (_ : SmoothOfRelativeDimension 1 c₁) (_ : GeometricallyIntegral c₁)
        (_ : IsProper c₂) (_ : SmoothOfRelativeDimension 1 c₂) (_ : GeometricallyIntegral c₂)
        (i₁ : SchemeHomOver c₁ (pullback.snd c s)) (i₂ : SchemeHomOver c₂ (pullback.snd c s))
        (_ : IsClosedImmersion i₁.1) (_ : IsClosedImmersion i₂.1) (n : ℕ),
        (∀ z : ↥(pullback c s), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base) ∧
        IsReduced (pullback i₁.1 i₂.1) ∧ Nat.card ↥(pullback i₁.1 i₂.1) = n ∧ 0 < n ∧
        ((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k) ∈ Set.range i₁.1.base \ Set.range i₂.1.base ∧
        ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) =
          (Set.range (pullback.fst i₁.1 i₂.1 ≫ i₁.1).base)ᶜ ∧
        Set.range i₁.1.base ∩ ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) =
          connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s))
            (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k)) ∧
        Set.range i₂.1.base ∩ ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) =
          ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) \
            connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s))
              (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k)) ∧
        (∃ W₁ : (pullback c s).Opens, (W₁ : Set ↥(pullback c s)) = (Set.range i₂.1.base)ᶜ ∧
          IsOpenImmersion ((i₁.1 ⁻¹ᵁ W₁).ι ≫ i₁.1)) ∧
        (∃ W₂ : (pullback c s).Opens, (W₂ : Set ↥(pullback c s)) = (Set.range i₁.1.base)ᶜ ∧
          IsOpenImmersion ((i₂.1 ⁻¹ᵁ W₂).ι ≫ i₂.1))) :
    ∃ D : RelativePic0Designation R c,
      Nonempty (RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) ∧
        Smooth D.toBase ∧ IsSeparated D.toBase ∧ QuasiCompact D.toBase ∧
        Surjective D.toBase ∧ GeometricallyConnected D.toBase := by sorry
