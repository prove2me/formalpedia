-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_forall_prime_exists_representsRelSubPic_algEquivZeroCut_baseChange_away_of_smoothLocus_of_twoGluedSmoothCurveDegenerations
-- name    : AlgebraicGeometry.RelPicard.forall_prime_exists_representsRelSubPic_algEquivZeroCut_baseChange_away_of_smoothLocus_of_twoGluedSmoothCurveDegenerations
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/f617cf0d-0602-5356-828a-205ad4c2132e
-- title:
--   Relative Pic⁰ over a basic open, two-component degenerations
-- statement:
--   Throughout, $R$ is a Noetherian reduced commutative ring, $C$ a scheme and $c\colon C\to\operatorname{Spec}R$ a proper flat morphism. Further data: a `C.TwoAffineOpenCover` $\mathcal V$, that is, two affine open subschemes $U_0,U_1$ of $C$ with $U_0\sqcup U_1=\top$ and $U_0\cap U_1$ affine.
--
--   The hypotheses come in the following groups.
--
--   *Global sections* (`hH0`): for every $R$-algebra $A$, the structure map $A\to\Gamma(C_A,\mathcal O)$ — where $C_A$ is the pullback of $c$ along $\operatorname{Spec}A\to\operatorname{Spec}R$ and the $A$-algebra structure on the global sections is the one induced by the projection to $\operatorname{Spec}A$ — is bijective.
--
--   *Smooth locus* ($U$, `hUmax`): an open subscheme $U\subseteq C$ such that $U\hookrightarrow C\to\operatorname{Spec}R$ is smooth of relative dimension $1$, and which is maximal with this property: every open $W\subseteq C$ with $W\to\operatorname{Spec}R$ smooth of relative dimension $1$ satisfies $W\le U$.
--
--   *Affine neighbourhoods in $U$* (`hcov`): for every affine open $V$ of $\operatorname{Spec}R$ and every finite set $F$ of points of $U$ all of whose images under $U\hookrightarrow C\to\operatorname{Spec}R$ lie in $V$, there is an affine open $W$ of the scheme $U$ contained in the preimage of $V$ and containing every point of $F$.
--
--   *Marked section* ($\varepsilon$, `hε`): an element of `SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c`, i.e. a morphism $\varepsilon\colon\operatorname{Spec}R\to C$ with $\varepsilon\circ c$ the identity, whose topological image is contained in $U$.
--
--   *Geometric fibres* (`hfib`, `hgred`, `hg` with the natural number $g$): for every algebraically closed field $k$ and every $x\colon\operatorname{Spec}k\to\operatorname{Spec}R$, (i) every invertible module $L$ on the fibre $C_x$ which satisfies `IsAlgEquivZero` for the structure morphism $C_x\to\operatorname{Spec}k$ — i.e. there are a locally of finite type geometrically integral $h\colon T'\to\operatorname{Spec}k$, an invertible module $M$ on $C_x\times_{\operatorname{Spec}k}T'$ and two sections $t_0,t_1$ of $h$ such that the pullback of $M$ along the base change at $t_0$ is isomorphic to the unit module and its pullback at $t_1$ is isomorphic to the pullback of $L$ — and which admits a nonzero morphism from the unit module, is itself isomorphic to the unit module; (ii) the fibre $C_x$ is reduced; (iii) for every two-affine open cover $\mathcal W$ of the fibre of $\operatorname{pr}_2\colon C\times_{\operatorname{Spec}R}\operatorname{Spec}R\to\operatorname{Spec}R$ at $x$, the $k$-dimension of the two-chart Čech $H^1$, namely $\Gamma(\mathcal O,\mathcal W_0\cap\mathcal W_1)$ modulo the image of the Čech differential, of the unit sheaf of modules computed with respect to $\mathcal W$ equals $g$.
--
--   *Pools of split points on both sides* ($d_0$, `hpool`): a natural number $d_0$ is fixed in advance, and for every prime $\mathfrak p$ of $R$ and all natural numbers $A_0,B_0,n_0$ there exist $f\in R\setminus\mathfrak p$, natural numbers $b,M,M'$ with $A_0b^{n_0}+B_0<M$ and $A_0b^{n_0}+B_0<M'$, a ring $R'$ which is an algebra over $R$ and over the localisation $R_f=\mathrm{Localization.Away}\,f$ compatibly, module-finite, étale and faithfully flat over $R_f$, and two families of $R_f$-algebras $B_i$ ($i\in\mathrm{Fin}\,M$) and $B'_i$ ($i\in\mathrm{Fin}\,M'$), each module-finite and étale over $R_f$, together with degrees $\deg i,\deg' i$ satisfying $1\le\deg i\le b$ and $1\le\deg' i\le b$, $R'$-algebra isomorphisms $R'\otimes_{R_f}B_i\simeq R'^{\deg i}$ and $R'\otimes_{R_f}B'_i\simeq R'^{\deg' i}$, and closed immersions $z_i\colon\operatorname{Spec}B_i\to C_{R_f}$, $z'_i\colon\operatorname{Spec}B'_i\to C_{R_f}$ into the base change $C_{R_f}=C\times_{\operatorname{Spec}R}\operatorname{Spec}R_f$, such that: each $z_i$ followed by the structure morphism $C_{R_f}\to\operatorname{Spec}R_f$ is the canonical morphism $\operatorname{Spec}B_i\to\operatorname{Spec}R_f$; the image of each $z_i$ lies in the preimage of $U$ under the first projection; the images of the $z_i$ are pairwise disjoint; for every algebraically closed field $k$, every $s\colon\operatorname{Spec}k\to\operatorname{Spec}R_f$ and every $i$, the preimage of the image of $z_i$ in the fibre at $s$ is contained in the connected component, inside the preimage of $U$ in that fibre, of the point cut out by the base-changed section $\varepsilon$ (the image of the closed point of $\operatorname{Spec}k$ under `sectionFibrePoint`); some $j$ has $\deg' j\le d_0$; each $z'_i$ is likewise a morphism over $R_f$, with image in the preimage of $U$, the images of the $z'_i$ being pairwise disjoint and disjoint from all images of the $z_i$; and for every algebraically closed $k$, every $s\colon\operatorname{Spec}k\to\operatorname{Spec}R_f$ and every $i\in\mathrm{Fin}\,M'$, if the fibre morphism at $s$ is not smooth, then the preimage of the image of $z'_i$ lies in the preimage of $U$ in that fibre with the connected component of the section point removed.
--
--   *Shape of the degenerate geometric fibres* (`hbad`): for every algebraically closed field $k$ and every $s\colon\operatorname{Spec}k\to\operatorname{Spec}R$ for which the fibre morphism $C_s\to\operatorname{Spec}k$ is not smooth, there are schemes $C_1,C_2$ with morphisms $c_1,c_2$ to $\operatorname{Spec}k$, both proper, smooth of relative dimension $1$ and geometrically integral, closed immersions $i_1\colon C_1\to C_s$ and $i_2\colon C_2\to C_s$ compatible with $c_1,c_2$ and the structure morphism of $C_s$, and a natural number $n$, such that: every point of $C_s$ lies in the image of $i_1$ or of $i_2$; the scheme-theoretic intersection $C_1\times_{C_s}C_2$ is reduced with exactly $n$ points and $n>0$; the point of $C_s$ determined by $\varepsilon$ lies in the image of $i_1$ and not in that of $i_2$; the preimage of $U$ in $C_s$ is exactly the complement of the image of the intersection in $C_s$; the image of $i_1$ meets the preimage of $U$ in precisely the connected component of the $\varepsilon$-point there, while the image of $i_2$ meets it in precisely the complement of that component; and there are opens $W_1,W_2$ of $C_s$ whose underlying sets are the complements of the images of $i_2$ and of $i_1$ respectively, such that $i_1$ restricted to $i_1^{-1}W_1$ and $i_2$ restricted to $i_2^{-1}W_2$ are open immersions.
--
--   Conclusion: for every prime $\mathfrak p$ of $R$ there exist $f\in R$ with $f\notin\mathfrak p$ and a `RelativePic0Designation` $D'$ for the base change $C_{R_f}\to\operatorname{Spec}R_f$, that is, a scheme $D'.P$ with a morphism $D'.\mathrm{toBase}\colon D'.P\to\operatorname{Spec}R_f$ and a section of it, such that all of the following hold: the type `RepresentsRelSubPic` for $C_{R_f}\to\operatorname{Spec}R_f$, the base-changed section of $\varepsilon$, the condition `algEquivZeroCut` and $D'$ is nonempty — i.e. there are a rigidified line bundle (an invertible module on $C_{R_f}\times_{\operatorname{Spec}R_f}D'.P$ together with a trivialisation of its restriction along the rigidifying section) whose geometric fibres are all algebraically equivalent to zero in the sense of `IsAlgEquivZero`, which is universal in the sense that for every $t\colon T\to\operatorname{Spec}R_f$ and every rigidified line bundle $M$ on $C_T$ with fibrewise algebraically trivial class there is a unique morphism $T\to D'.P$ over $\operatorname{Spec}R_f$ pulling the universal bundle back to a bundle isomorphic to $M$, and whose pullback along the zero section of $D'$ is isomorphic to the unit module; and, moreover, $D'.\mathrm{toBase}$ is smooth, separated, quasi-compact, surjective and geometrically connected.
--
--   This is the local (per-basic-open) existence statement for the relative $\mathrm{Pic}^0$ of a pointed proper flat curve whose degenerate geometric fibres are two smooth proper geometrically integral curves meeting in finitely many points: over a suitable $D(f)$ around each prime of $R$ the subfunctor of rigidified line bundles that are fibrewise algebraically equivalent to zero is representable by a smooth, separated, quasi-compact, surjective and geometrically connected scheme. It is used by [`AlgebraicGeometry.RelPicard.exists_representsRelSubPic_algEquivZeroCut_of_smoothLocus_of_twoGluedSmoothCurveDegenerations`](thm.html#AlgebraicGeometry.RelPicard.exists_representsRelSubPic_algEquivZeroCut_of_smoothLocus_of_twoGluedSmoothCurveDegenerations), where the local representing objects are assembled over $\operatorname{Spec}R$, in the construction of Jacobians with semistable reduction used later for the Galois representations attached to modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_forall_prime_exists_representsRelSubPic_algEquivZeroCut_baseChange_away_of_smoothLocus_of_twoGluedSmoothCurveDegenerations.lean

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

theorem AlgebraicGeometry.RelPicard.forall_prime_exists_representsRelSubPic_algEquivZeroCut_baseChange_away_of_smoothLocus_of_twoGluedSmoothCurveDegenerations
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
    ∀ 𝔭 : PrimeSpectrum R, ∃ (f : R) (_ : f ∉ 𝔭.asIdeal)
      (D' : RelativePic0Designation (Localization.Away f) (baseChange R c (Localization.Away f))),
      Nonempty (RepresentsRelSubPic (baseChange R c (Localization.Away f))
          (sectionBaseChange (Localization.Away f) ε)
          (algEquivZeroCut (baseChange R c (Localization.Away f))
            (sectionBaseChange (Localization.Away f) ε)) D') ∧
        Smooth D'.toBase ∧ IsSeparated D'.toBase ∧ QuasiCompact D'.toBase ∧
        Surjective D'.toBase ∧ GeometricallyConnected D'.toBase := by sorry
