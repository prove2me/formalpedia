-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_forall_prime_exists_representsRelSubPic_algEquivZeroCut_baseChange_away_of_smoothLocus_of_twoLineDegenerations
-- name    : AlgebraicGeometry.RelPicard.forall_prime_exists_representsRelSubPic_algEquivZeroCut_baseChange_away_of_smoothLocus_of_twoLineDegenerations
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/f50f438c-bba8-5b14-bf57-4f5f4d02466b
-- title:
--   Relative Pic⁰ on a basic open, two-line degenerations
-- statement:
--   Throughout, $R$ is a reduced Noetherian commutative ring, $C$ is a scheme and $c\colon C\to\operatorname{Spec}R$ is proper and flat, and $\mathcal V$ is a `Scheme.TwoAffineOpenCover` of $C$, i.e. two affine opens $U_0,U_1$ with affine intersection covering $C$.
--
--   The cohomological hypothesis `hH0` requires that for every $R$-algebra $A$ the structure map $A\to\Gamma(C\times_{\operatorname{Spec}R}\operatorname{Spec}A,\top)$, taken with the algebra structure coming from the projection to $\operatorname{Spec}A$, be bijective; that is, $c_*\mathcal O_C=\mathcal O$ universally over $R$.
--
--   The smooth locus data consist of an open $U\subseteq C$ such that $U\hookrightarrow C$ followed by $c$ is smooth of relative dimension $1$, together with `hUmax`, which states that every open $W\subseteq C$ with $W\hookrightarrow C$ followed by $c$ smooth of relative dimension $1$ satisfies $W\le U$ (so $U$ is the largest such open), and `hcov`, which states that for every affine open $V$ of $\operatorname{Spec}R$ and every finite set $F$ of points of $U$ all of whose images under $U\hookrightarrow C$ followed by $c$ lie in $V$, there is an affine open $W$ of the scheme $U$ contained in the preimage of $V$ and containing $F$.
--
--   Further, $\varepsilon$ is a section of $c$, i.e. a morphism $\operatorname{Spec}R\to C$ whose composite with $c$ is the identity, and `hε` requires its image to be contained in $U$.
--
--   The fibre hypothesis `hfib` requires: for every algebraically closed field $k$, every $k$-point $x\colon\operatorname{Spec}k\to\operatorname{Spec}R$ and every module $L$ on the fibre $C\times_{\operatorname{Spec}R}\operatorname{Spec}k$ which is invertible (locally isomorphic to the unit) and satisfies `IsAlgEquivZero` for the projection to $\operatorname{Spec}k$ — that is, there are a locally-of-finite-type geometrically integral $h\colon T'\to\operatorname{Spec}k$, an invertible module $M$ on the corresponding pullback and two sections $t_0,t_1$ of $h$ such that $M$ restricted along $t_0$ is isomorphic to the unit and $M$ restricted along $t_1$ is isomorphic to the pullback of $L$ — every nonzero morphism from the unit to $L$ forces $L$ to be isomorphic to the unit.
--
--   The hypothesis `hgred` requires every geometric fibre $C\times_{\operatorname{Spec}R}\operatorname{Spec}k$, for $k$ algebraically closed, to be reduced. A natural number $g$ is given, and `hg` requires that for every algebraically closed $k$, every $k$-point $x$ of $\operatorname{Spec}R$ and every two-affine open cover $\mathcal W$ of the fibre of $C\times_{\operatorname{Spec}R}\operatorname{Spec}R$ over $x$, the $k$-dimension of the degree-one two-chart Čech cohomology `H1` of the sections of the structure sheaf of modules with respect to $\mathcal W$ equals $g$.
--
--   The pool hypothesis `hpool` requires that for every prime $\mathfrak p$ of $R$ and all natural numbers $A_0,B_0,n_0$ there exist $f\notin\mathfrak p$, natural numbers $b,M$ with $A_0b^{n_0}+B_0<M$, an algebra $R'$ over $R$ and over the localisation $R_f=\,$`Localization.Away f` (compatibly, forming a scalar tower) which is finite, étale and faithfully flat over $R_f$, finite étale $R_f$-algebras $B_i$ for $i\in\operatorname{Fin}M$, degrees $\deg i$ with $1\le\deg i\le b$, $R'$-algebra isomorphisms $R'\otimes_{R_f}B_i\cong R'^{\deg i}$, and closed immersions $z_i\colon\operatorname{Spec}B_i\to C\times_{\operatorname{Spec}R}\operatorname{Spec}R_f$, subject to four conditions: each $z_i$ followed by the base-changed structure morphism is the structure map $\operatorname{Spec}B_i\to\operatorname{Spec}R_f$; the image of each $z_i$ lies in the preimage of $U$; the images of the $z_i$ are pairwise disjoint; and for every algebraically closed field $k$, every $k$-point $s$ of $\operatorname{Spec}R_f$ and every $i$, the preimage in the fibre over $s$ of the image of $z_i$ is contained in the connected component, inside the preimage of $U$, of the point of that fibre determined by the base-changed section `sectionBaseChange (Localization.Away f) ε` via `sectionFibrePoint` at the closed point of $\operatorname{Spec}k$.
--
--   The degeneration hypothesis `hbad` requires that for every algebraically closed field $k$ and every $k$-point $s$ of $\operatorname{Spec}R$ whose fibre $C_s=C\times_{\operatorname{Spec}R}\operatorname{Spec}k$ is not smooth over $\operatorname{Spec}k$, there exist two curve models $M_1,M_2$ of $\mathrm{RatFunc}\,k$ over $k$ (each a proper smooth integral curve of relative dimension one over $k$ with function field identified with $k(T)$ and closed points in bijection with the places, as in `CurveModel`), closed immersions $i_1\colon M_1.C\to C_s$ and $i_2\colon M_2.C\to C_s$, a natural number $n$, families $a,b\colon\operatorname{Fin}n\to k^{\times}$ and a two-affine open cover $\mathcal W_0$ of $C_s$ such that: $i_1$ and $i_2$ are morphisms over $\operatorname{Spec}k$ (their composites with the projection are the structure maps of $M_1,M_2$); the images of $i_1$ and $i_2$ cover $C_s$; $a$ is injective; for each $i$ the point of $M_1.C$ at the place of $a_i$ and the point of $M_2.C$ at the place of $b_i$ have the same image; conversely any pair of points with the same image is of that form; the scheme-theoretic intersection $M_1.C\times_{C_s}M_2.C$ is reduced; the preimages under $i_1$ and $i_2$ of $\mathcal W_0.U_0$ are the complements of the points at infinity, and the preimages of $\mathcal W_0.U_1$ are the complements of the points at the place of $0$; $i_1$ carries the point at infinity of $M_1.C$ to the point of $C_s$ determined by $\varepsilon$ via `sectionFibrePoint`; the intersection of the image of $i_1$ with the preimage of $U$ is exactly the connected component of that preimage containing this $\varepsilon$-point; the nodal points $i_1$ of the places of the $a_i$ lie outside the preimage of $U$; every point of $C_s$ other than these lies in the preimage of $U$; and there is an open $W_1\subseteq C_s$ whose underlying set is the complement of the image of $i_2$ and for which the inclusion of $i_1^{-1}W_1$ followed by $i_1$ is an open immersion.
--
--   Conclusion: for every prime $\mathfrak p$ of $R$ there exist an element $f\in R$ with $f\notin\mathfrak p$ and a `RelativePic0Designation` $D'$ over $R_f=\,$`Localization.Away f` for the base-changed curve $C_{R_f}\to\operatorname{Spec}R_f$ — that is, a scheme $D'.P$ with a structure morphism $D'.\mathrm{toBase}\colon D'.P\to\operatorname{Spec}R_f$ and a section of it — such that the following hold. First, the type `RepresentsRelSubPic` for $C_{R_f}$, the base-changed section `sectionBaseChange (Localization.Away f) ε` and the condition `algEquivZeroCut` at $D'$ is nonempty: there is a rigidified line bundle (a Poincaré bundle) on $C_{R_f}\times_{\operatorname{Spec}R_f}D'.P$ satisfying the condition, whose formation of pullbacks gives, for every $R_f$-scheme $T$ and every rigidified line bundle $\mathcal M$ on $C_{R_f}\times_{\operatorname{Spec}R_f}T$ satisfying the condition, a unique $T$-point of $D'.P$ over $\operatorname{Spec}R_f$ whose pullback of the Poincaré bundle is isomorphic to $\mathcal M$, and whose pullback along the zero section is isomorphic to the unit. Here `algEquivZeroCut` is the subfunctor condition selecting those rigidified line bundles that are fibrewise algebraically equivalent to zero, in the sense that for every algebraically closed $k$ and every $k$-point $s$ of the parameter scheme the restriction to the fibre satisfies `IsAlgEquivZero` as described above. Second, $D'.\mathrm{toBase}$ is smooth. Third, it is separated. Fourth, it is quasi-compact. Fifth, it is surjective. Sixth, it is geometrically connected.
--
--   This is the local existence statement for the relative $\mathrm{Pic}^0$ (the Jacobian) of a proper flat pointed curve over a reduced Noetherian base whose non-smooth geometric fibres are transversal gluings of two coordinatised projective lines: over a Zariski-open neighbourhood $\operatorname{Spec}R_f$ of each prime, the algebraic-equivalence-to-zero part of the rigidified relative Picard functor is represented by a smooth, separated, quasi-compact, surjective and geometrically connected scheme over $R_f$. It is the input, patch by patch, for [`AlgebraicGeometry.RelPicard.exists_representsRelSubPic_algEquivZeroCut_of_smoothLocus_of_twoLineDegenerations`](thm.html#AlgebraicGeometry.RelPicard.exists_representsRelSubPic_algEquivZeroCut_of_smoothLocus_of_twoLineDegenerations), which glues the local designations over a basic-open cover of $\operatorname{Spec}R$ into a global one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_forall_prime_exists_representsRelSubPic_algEquivZeroCut_baseChange_away_of_smoothLocus_of_twoLineDegenerations.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian AlgebraicCurve

theorem AlgebraicGeometry.RelPicard.forall_prime_exists_representsRelSubPic_algEquivZeroCut_baseChange_away_of_smoothLocus_of_twoLineDegenerations
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

    (hpool : ∀ (𝔭 : PrimeSpectrum R) (A₀ B₀ n₀ : ℕ), ∃ (f : R) (_ : f ∉ 𝔭.asIdeal) (b M : ℕ) (_ : A₀ * b ^ n₀ + B₀ < M)
      (R' : Type u) (_ : CommRing R') (_ : Algebra R R')
      (_ : Algebra (Localization.Away f) R') (_ : IsScalarTower R (Localization.Away f) R')
      (_ : Module.Finite (Localization.Away f) R') (_ : Algebra.Etale (Localization.Away f) R')
      (_ : Module.FaithfullyFlat (Localization.Away f) R')
      (B : Fin M → Type u) (_ : ∀ i, CommRing (B i)) (_ : ∀ i, Algebra (Localization.Away f) (B i))
      (_ : ∀ i, Module.Finite (Localization.Away f) (B i)) (_ : ∀ i, Algebra.Etale (Localization.Away f) (B i))
      (deg : Fin M → ℕ) (_ : ∀ i, 1 ≤ deg i) (_ : ∀ i, deg i ≤ b)
      (φ : ∀ i, TensorProduct (Localization.Away f) R' (B i) ≃ₐ[R'] (Fin (deg i) → R'))
      (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ pullback c (specMap R (Localization.Away f)))
      (_ : ∀ i, IsClosedImmersion (z i)),
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
            (((sectionFibrePoint (sectionBaseChange (Localization.Away f) ε) s).1).base (IsLocalRing.closedPoint k))))

    (hbad : ∀ (k : Type u) [Field k] [IsAlgClosed k] [DecidableEq (RatFunc k)]
      (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)), ¬ Smooth (pullback.snd c s) →
      ∃ (M₁ M₂ : CurveModel k (RatFunc k)) (i₁ : M₁.C ⟶ pullback c s) (i₂ : M₂.C ⟶ pullback c s)
        (_ : IsClosedImmersion i₁) (_ : IsClosedImmersion i₂)
        (n : ℕ) (a b : Fin n → kˣ) (𝒲₀ : (pullback c s).TwoAffineOpenCover),
        i₁ ≫ pullback.snd c s = M₁.toBase ∧ i₂ ≫ pullback.snd c s = M₂.toBase ∧
        Set.range i₁.base ∪ Set.range i₂.base = Set.univ ∧
        Function.Injective a ∧
        (∀ i, i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 =
          i₂.base (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k (b i : k))).1) ∧
        (∀ (p : M₁.C) (q : M₂.C), i₁.base p = i₂.base q →
          ∃ i, p = (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 ∧
            q = (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k (b i : k))).1) ∧
        IsReduced (pullback i₁ i₂) ∧
        ((i₁ ⁻¹ᵁ 𝒲₀.U0 : M₁.C.Opens) : Set M₁.C) =
          {(M₁.placeEquiv.symm (RationalFunctionField.placeInfty k)).1}ᶜ ∧
        ((i₂ ⁻¹ᵁ 𝒲₀.U0 : M₂.C.Opens) : Set M₂.C) =
          {(M₂.placeEquiv.symm (RationalFunctionField.placeInfty k)).1}ᶜ ∧
        ((i₁ ⁻¹ᵁ 𝒲₀.U1 : M₁.C.Opens) : Set M₁.C) =
          {(M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k 0)).1}ᶜ ∧
        ((i₂ ⁻¹ᵁ 𝒲₀.U1 : M₂.C.Opens) : Set M₂.C) =
          {(M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k 0)).1}ᶜ ∧
        i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeInfty k)).1 = ((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k) ∧
        Set.range i₁.base ∩ ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) =
          connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k)) ∧
        (∀ i, i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 ∉
          (pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens)) ∧
        (∀ y : ↥(pullback c s),
          (∀ i, y ≠ i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1) →
            y ∈ (pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens)) ∧
        (∃ W₁ : (pullback c s).Opens, (W₁ : Set ↥(pullback c s)) = (Set.range i₂.base)ᶜ ∧
          IsOpenImmersion ((i₁ ⁻¹ᵁ W₁).ι ≫ i₁))) :
    ∀ 𝔭 : PrimeSpectrum R, ∃ (f : R) (_ : f ∉ 𝔭.asIdeal)
      (D' : RelativePic0Designation (Localization.Away f) (baseChange R c (Localization.Away f))),
      Nonempty (RepresentsRelSubPic (baseChange R c (Localization.Away f))
          (sectionBaseChange (Localization.Away f) ε)
          (algEquivZeroCut (baseChange R c (Localization.Away f))
            (sectionBaseChange (Localization.Away f) ε)) D') ∧
        Smooth D'.toBase ∧ IsSeparated D'.toBase ∧ QuasiCompact D'.toBase ∧
        Surjective D'.toBase ∧ GeometricallyConnected D'.toBase := by sorry
