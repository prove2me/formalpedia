-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_split_injective_forall_subsingleton_H1_lineBundle_and_support_subset_of_twoSidedBlocks_of_bijective_sections
-- name    : AlgebraicGeometry.RelPicard.exists_split_injective_forall_subsingleton_H1_lineBundle_and_support_subset_of_twoSidedBlocks_of_bijective_sections
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/9f17a82a-98df-5bb2-b3a4-411b23cd650a
-- title:
--   Block general position for the twist 𝒪(E_Ω)
-- statement:
--   Throughout, $R$ is a commutative ring and $c : C \to \operatorname{Spec} R$ is a proper flat morphism of schemes, $\mathcal V$ is a two-affine open cover of $C$ (two affine opens $U_0,U_1$ with affine intersection and union $C$), and $\varepsilon$ is a section of $c$, i.e. a morphism $\operatorname{Spec} R \to C$ whose composite with $c$ is the identity.
--
--   The geometric hypotheses on $c$ are as follows. The hypothesis `hH0` requires that for every $R$-algebra $A$ the structure map $A \to \Gamma(C\times_{\operatorname{Spec} R}\operatorname{Spec} A,\ \top)$ be bijective, the $R$-algebra structure on the global sections being the one induced by the projection to $\operatorname{Spec} A$; thus formation of global sections of the structure sheaf is universally trivial. An open subscheme $U \subseteq C$ is given whose composite $U \hookrightarrow C \to \operatorname{Spec} R$ is smooth of relative dimension $1$. The hypothesis `hεA` requires the image of $\varepsilon$ to lie in $U$; `hgoodU` requires that for every algebraically closed field $k$ and every $x : \operatorname{Spec} k \to \operatorname{Spec} R$ with smooth fibre $\operatorname{pr}_2 : C\times_{\operatorname{Spec}R}\operatorname{Spec} k \to \operatorname{Spec} k$, the image of the first projection of that fibre lie in $U$ (smooth geometric fibres are contained in $U$); `hgred` requires every geometric fibre $C\times_{\operatorname{Spec}R}\operatorname{Spec}k$ to be reduced. A natural number $g$ is given, and `hg` requires that for every algebraically closed field $k$, every $x : \operatorname{Spec} k \to \operatorname{Spec} R$ and every two-affine open cover $\mathcal W$ of the fibre, the $k$-dimension of the two-chart Čech $H^1$ of the structure sheaf (the unit module) computed from $\mathcal W$ relative to `fibreAt c (𝟙 _) x` equal $g$; here $H^1$ of a two-chart datum is the cokernel of the Čech differential $(m_0,m_1)\mapsto -r_0m_0+r_1m_1$ on the sections over the two charts.
--
--   The degeneration hypothesis `hbad` requires that for every algebraically closed field $k$ and every $s : \operatorname{Spec} k \to \operatorname{Spec} R$ with non-smooth fibre $C_s := C\times_{\operatorname{Spec}R}\operatorname{Spec} k$ there exist two proper, smooth of relative dimension $1$, geometrically integral curves $c_1 : C_1 \to \operatorname{Spec} k$, $c_2 : C_2 \to \operatorname{Spec} k$, closed immersions $i_1,i_2$ of $C_1,C_2$ into $C_s$ over $\operatorname{Spec} k$, and $n \in \mathbb N$ such that: every point of $C_s$ lies in the image of $i_1$ or of $i_2$; the scheme-theoretic intersection $C_1\times_{C_s}C_2$ is reduced with exactly $n$ points and $n>0$; the $k$-point of $C_s$ determined by $\varepsilon$ (the closed point under `sectionFibrePoint ε s`) lies in the image of $i_1$ but not of $i_2$; the preimage of $U$ in $C_s$ is the complement of the image of the intersection $C_1\times_{C_s}C_2 \to C_s$; the intersection of the image of $i_1$ with that preimage is the connected component, inside the preimage of $U$, of the $\varepsilon$-point, while the intersection of the image of $i_2$ with the preimage of $U$ is its complement in the preimage of $U$; and there are opens $W_1,W_2$ of $C_s$ whose underlying sets are the complements of the images of $i_2$, respectively $i_1$, such that the restrictions $i_1^{-1}W_1 \hookrightarrow C_1$ followed by $i_1$, and $i_2^{-1}W_2 \hookrightarrow C_2$ followed by $i_2$, are open immersions. Thus every degenerate geometric fibre is a union of two smooth geometrically integral curves meeting in $n>0$ points, the $\varepsilon$-component being the first.
--
--   Two pools of étale multisections are given, together with a splitting algebra. An $R$-algebra $A$ is fixed which is finite and faithfully flat as an $R$-module. For the first pool: natural numbers $M$, a family $B : \operatorname{Fin} M \to \mathrm{Type}$ of commutative rings, each a finite étale $R$-algebra, degrees $\deg i$ with $\deg i \ge 1$ (`hdeg`), $A$-algebra isomorphisms $\varphi_i : A\otimes_R B_i \cong A^{\deg i}$ (so each $B_i$ splits completely over $A$), and closed immersions $z_i : \operatorname{Spec} B_i \to C$ with $z_i$ followed by $c$ equal to $\operatorname{Spec}$ of the structure map $R \to B_i$ (`hz`), with images contained in $U$ (`hzU`) and pairwise disjoint (`hzdisj`); the hypothesis `hzε` requires that for every algebraically closed field $k$, every $s : \operatorname{Spec} k \to \operatorname{Spec} R$ and every $i$, the preimage in $C_s$ of the image of $z_i$ be contained in the connected component, inside the preimage of $U$, of the $\varepsilon$-point. For the second pool the data $M'$, $B'$, $\deg'$ with $\deg' i \ge 1$ (`hdeg'`), isomorphisms $\varphi'_i : A\otimes_R B'_i\cong A^{\deg' i}$, closed immersions $z'_i$ over $\operatorname{Spec} B'_i$ (`hz'`), images in $U$ (`hz'U`), pairwise disjoint images (`hz'disj`) and images disjoint from all images of the first pool (`hzz'`) are required, together with `hz'ε`: for every algebraically closed field $k$, every $s$ with non-smooth fibre and every $i$, the preimage in $C_s$ of the image of $z'_i$ lies in the preimage of $U$ minus the connected component of the $\varepsilon$-point. Thus the first pool is concentrated on the $\varepsilon$-component and the second, over degenerate fibres, on the other component.
--
--   The numerical hypotheses are: natural numbers $r,r'$, an index $i_0 : \operatorname{Fin} M'$ and $e$ with $g+e = r + r'\deg'(i_0)$ (`he`), $2g+1 \le r$ (`hr`) and $2g+1 \le r'$ (`hr'`); a bound $b$ with $\deg i \le b$ for all $i$ (`hdegb`) and $\deg' i \le b$ for all $i$ (`hdeg'b`); and the counting inequalities $(g+2)(r+r'b)b^{e}+e < M$ (`hMlt`) and $(g+2)(r+r'b)b^{e}+e+1 < M'$ (`hM'lt`).
--
--   Finally, $\rho$ is a natural number with $\rho = r + r'\deg'(i_0)$ (`hρ`) and $E$ is a relative effective Cartier divisor for $c$ of degree $\rho$ over the identity of $\operatorname{Spec} R$: an ideal sheaf datum $E.I$ on $C\times_{\operatorname{Spec}R}\operatorname{Spec}R$ whose closed subscheme is finite, flat and locally of finite presentation over the base with fibre rank $\rho$ at every point. The hypothesis `hEI` requires $E.I = (\mathrm{sectionIdeal}\ c\ \varepsilon)^r \cdot \mathcal I^{r'}$, where the first factor is the ideal of the section induced by $\varepsilon$ and $\mathcal I$ is the kernel ideal of the morphism $\operatorname{Spec} B'_{i_0} \to C\times_{\operatorname{Spec}R}\operatorname{Spec}R$ lifting $z'_{i_0}$ and $\operatorname{Spec}$ of $R \to B'_{i_0}$.
--
--   Under these hypotheses the conclusion is: for every algebraically closed field $\Omega$ which is an $R$-algebra, writing $C_\Omega := C\times_{\operatorname{Spec}R}\operatorname{Spec}\Omega$, and for every module $L_0$ on $C_\Omega$ which is invertible (locally on $C_\Omega$ isomorphic to the unit module) and satisfies `IsAlgEquivZero` for $\operatorname{pr}_2 : C_\Omega\to\operatorname{Spec}\Omega$ — that is, there are a locally of finite type, geometrically integral $h : T' \to \operatorname{Spec}\Omega$, an invertible module $M$ on $C_\Omega\times_{\operatorname{Spec}\Omega}T'$ and two sections $t_0,t_1$ of $h$ such that the pullback of $M$ along the base change of $t_0$ is isomorphic to the unit module and its pullback along the base change of $t_1$ is isomorphic to the pullback of $L_0$ — there exist $e_1,e_2 \in \mathbb N$ with $e_1+e_2=e$ and injective maps $a : \operatorname{Fin} e_1 \to \operatorname{Fin} M$ and $a' : \operatorname{Fin} e_2 \to \operatorname{Fin} M'$ with the following property. For all families $v$ of $e_1$ and $v'$ of $e_2$ sections of $\operatorname{pr}_2 : C_\Omega \to \operatorname{Spec}\Omega$ (that is, morphisms $\operatorname{Spec}\Omega \to C_\Omega$ whose composite with $\operatorname{pr}_2$ is the identity) such that each $v_j$ factors, after composition with the projection $C_\Omega \to C$, as $\operatorname{Spec}$ of some $R$-algebra homomorphism $B_{a(j)} \to \Omega$ followed by $z_{a(j)}$, and each $v'_j$ likewise factors through $z'_{a'(j)}$ by some $R$-algebra homomorphism $B'_{a'(j)}\to\Omega$, both of the following hold for the module
--   $$\mathcal F := L_0 \otimes \Big( \mathcal O(E_\Omega) \otimes \big(\textstyle\prod_j \ker v_j \cdot \prod_j \ker v'_j\big)^{\mathrm{module}}\Big),$$
--   where $\mathcal O(E_\Omega)$ denotes the line bundle of the pullback of $E$ along $\operatorname{Spec}\Omega\to\operatorname{Spec}R$, i.e. the dual of the module attached to its ideal, and the last factor is the module attached to the product of the kernel ideals of the points $v_j$ and $v'_j$:
--
--   (1) for every two-affine open cover $\mathcal W$ of $C_\Omega$, the two-chart Čech $H^1$ of $\mathcal F$ computed from $\mathcal W$ relative to $\operatorname{pr}_2$ is a subsingleton, i.e. vanishes;
--
--   (2) for every morphism $\tau$ from the unit module of $C_\Omega$ to $\mathcal F$ with $\tau \ne 0$, the support of the zero-scheme ideal of $\tau$ (the infimum of the ideal sheaf data dominating the coefficient ideals of $\tau$ on affine opens) is contained, as a subset of $C_\Omega$, in the preimage of $U$ under the projection $C_\Omega \to C$.
--
--   This is the two-sided block general-position statement in the currency of the twist $\mathcal O(E_\Omega)$ by a relative effective Cartier divisor $E$ of degree $g+e$ over the base, rather than in terms of the explicit product of point ideals $I_\varepsilon^{\,r}\cdot I_{z'_{i_0}}^{\,r'}$: after removing $e$ points taken from the two pools it provides vanishing of the two-chart Čech $H^1$ and the statement that nonzero sections vanish only inside the relative smooth locus $U$. It feeds the construction of charts for the relative Picard functor, being cited by [`AlgebraicGeometry.RelPicard.exists_chart_subsingleton_H1_and_support_subset_fibre_of_twoSidedBlocks_of_injective`](thm.html#AlgebraicGeometry.RelPicard.exists_chart_subsingleton_H1_and_support_subset_fibre_of_twoSidedBlocks_of_injective) and by [`AlgebraicGeometry.RelPicard.forall_prime_exists_representsRelSubPic_algEquivZeroCut_baseChange_away_of_smoothLocus_of_twoGluedSmoothCurveDegenerations`](thm.html#AlgebraicGeometry.RelPicard.forall_prime_exists_representsRelSubPic_algEquivZeroCut_baseChange_away_of_smoothLocus_of_twoGluedSmoothCurveDegenerations).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_split_injective_forall_subsingleton_H1_lineBundle_and_support_subset_of_twoSidedBlocks_of_bijective_sections.lean

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
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra
open AlgebraicGeometry.RelPicard

open AlgebraicGeometry.SmoothProperCurve
open AlgebraicCurve

theorem AlgebraicGeometry.RelPicard.exists_split_injective_forall_subsingleton_H1_lineBundle_and_support_subset_of_twoSidedBlocks_of_bijective_sections
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c] [Flat c]

    (𝒱 : C.TwoAffineOpenCover)
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (hεA : Set.range ε.1 ⊆ (U : Set C))
    (hgoodU : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)),
      Smooth (pullback.snd c x) → Set.range (pullback.fst c x).base ⊆ (U : Set C))
    (hgred : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)), IsReduced (pullback c x))
    (g : ℕ)
    (hg : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover),
      Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
        (SheafOfModules.unit (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).ringCatSheaf)).H1 = g)

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
          IsOpenImmersion ((i₂.1 ⁻¹ᵁ W₂).ι ≫ i₂.1)))
    (A : Type u) [CommRing A] [Algebra R A] [Module.Finite R A] [Module.FaithfullyFlat R A]

    {M M' : ℕ} (B : Fin M → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    [∀ i, Module.Finite R (B i)] [∀ i, Algebra.Etale R (B i)]
    (deg : Fin M → ℕ) (hdeg : ∀ i, 1 ≤ deg i) (φ : ∀ i, TensorProduct R A (B i) ≃ₐ[A] (Fin (deg i) → A))
    (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ C) [∀ i, IsClosedImmersion (z i)]
    (hz : ∀ i, z i ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R (B i))))
    (hzU : ∀ i, Set.range (z i).base ⊆ (U : Set C))
    (hzdisj : Pairwise fun i j => Disjoint (Set.range (z i).base) (Set.range (z j).base))
    (hzε : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) (i : Fin M),
      (pullback.fst c s).base ⁻¹' Set.range (z i).base ⊆
        connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s))
          (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k)))

    (B' : Fin M' → Type u) [∀ i, CommRing (B' i)] [∀ i, Algebra R (B' i)]
    [∀ i, Module.Finite R (B' i)] [∀ i, Algebra.Etale R (B' i)]
    (deg' : Fin M' → ℕ) (hdeg' : ∀ i, 1 ≤ deg' i) (φ' : ∀ i, TensorProduct R A (B' i) ≃ₐ[A] (Fin (deg' i) → A))
    (z' : ∀ i, Spec (CommRingCat.of (B' i)) ⟶ C) [∀ i, IsClosedImmersion (z' i)]
    (hz' : ∀ i, z' i ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R (B' i))))
    (hz'U : ∀ i, Set.range (z' i).base ⊆ (U : Set C))
    (hz'disj : Pairwise fun i j => Disjoint (Set.range (z' i).base) (Set.range (z' j).base))
    (hzz' : ∀ i j, Disjoint (Set.range (z i).base) (Set.range (z' j).base))
    (hz'ε : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) (i : Fin M'),
      ¬ Smooth (pullback.snd c s) →
      (pullback.fst c s).base ⁻¹' Set.range (z' i).base ⊆
        ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) \
          connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s))
            (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k)))

    (r r' : ℕ) (i₀ : Fin M') (e : ℕ) (he : g + e = r + r' * deg' i₀) (hr : 2 * g + 1 ≤ r) (hr' : 2 * g + 1 ≤ r')
    (b : ℕ) (hdegb : ∀ i, deg i ≤ b) (hdeg'b : ∀ i, deg' i ≤ b)
    (hMlt : (g + 2) * (r + r' * b) * b ^ e + e < M) (hM'lt : (g + 2) * (r + r' * b) * b ^ e + e + 1 < M')

    (ρ : ℕ) (hρ : ρ = r + r' * deg' i₀)
    (E : RelEffCartierDiv c ρ (𝟙 (Spec (CommRingCat.of R))))
    (hEI : E.I = (sectionIdeal c ε (𝟙 (Spec (CommRingCat.of R)))) ^ r *
      ((pullback.lift (z' i₀) (Spec.map (CommRingCat.ofHom (algebraMap R (B' i₀)))) (by rw [Category.comp_id]; exact hz' i₀)).ker) ^ r') :
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra R Ω]
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
              ((pullback.fst c (SmoothProperCurve.specMap R Ω)) ⁻¹ᵁ U : Set ↥(pullback c (SmoothProperCurve.specMap R Ω)))) := by sorry
