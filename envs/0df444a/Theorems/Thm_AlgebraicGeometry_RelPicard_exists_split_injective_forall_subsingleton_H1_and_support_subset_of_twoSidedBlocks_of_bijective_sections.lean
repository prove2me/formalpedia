-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_split_injective_forall_subsingleton_H1_and_support_subset_of_twoSidedBlocks_of_bijective_sections
-- name    : AlgebraicGeometry.RelPicard.exists_split_injective_forall_subsingleton_H1_and_support_subset_of_twoSidedBlocks_of_bijective_sections
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/2bd655ed-c6c8-5c40-99e0-bbb5034a6344
-- title:
--   Two-sided block general position on the geometric fibres of a degenerating curve
-- statement:
--   Throughout, $R$ is a commutative ring and $c \colon C \to \operatorname{Spec} R$ is a proper, flat morphism of schemes.
--
--   **Global data on $C$.** A two-chart affine open cover $\mathcal V$ of $C$ is given (two affine opens $U_0, U_1$ with $U_0 \sqcup U_1 = \top$ and $U_0 \sqcap U_1$ affine). The hypothesis `hH0` requires that for every $R$-algebra $A$ the structure map $A \to \Gamma(C \times_{\operatorname{Spec} R} \operatorname{Spec} A, \top)$ is bijective, the $A$-algebra structure on global sections being the one induced by the projection to $\operatorname{Spec} A$. Further given are a section $\varepsilon$ of $c$, that is a morphism $\varepsilon_1 \colon \operatorname{Spec} R \to C$ with $\varepsilon_1 \circ$ followed by $c$ equal to the identity, and an open subscheme $U \subseteq C$ such that the inclusion followed by $c$ is smooth of relative dimension $1$. The hypothesis `hεA` requires that the image of $\varepsilon_1$ on points lies in $U$; `hgoodU` requires that for every algebraically closed field $k$ and every $x \colon \operatorname{Spec} k \to \operatorname{Spec} R$ for which the fibre projection $\operatorname{pr}_2 \colon C \times_{\operatorname{Spec} R} \operatorname{Spec} k \to \operatorname{Spec} k$ is smooth, the image of the first projection of that fibre lies in $U$ (smooth geometric fibres are contained in $U$); `hgred` requires every such geometric fibre to be reduced. Finally a natural number $g$ is given together with `hg`: for every algebraically closed field $k$, every $x \colon \operatorname{Spec} k \to \operatorname{Spec} R$ and every two-chart affine open cover $\mathcal W$ of the fibre at $x$ of the trivial base change of $c$, the $k$-dimension of the degree-one cohomology $H^1 = M_{01}/\operatorname{im}(-r_0 \oplus r_1)$ of the two-chart Čech complex of the structure sheaf on that fibre equals $g$.
--
--   **The degeneration hypothesis `hbad`.** For every algebraically closed field $k$ and every $s \colon \operatorname{Spec} k \to \operatorname{Spec} R$ such that $\operatorname{pr}_2 \colon C_s := C \times_{\operatorname{Spec} R} \operatorname{Spec} k \to \operatorname{Spec} k$ is not smooth, there exist two schemes $C_1, C_2$ with structure morphisms $c_1, c_2$ to $\operatorname{Spec} k$ that are proper, smooth of relative dimension $1$ and geometrically integral, closed immersions $i_1 \colon C_1 \to C_s$ and $i_2 \colon C_2 \to C_s$ over $\operatorname{Spec} k$ (that is, $i_\nu$ followed by $\operatorname{pr}_2$ equals $c_\nu$), and a natural number $n$, such that: every point of $C_s$ lies in the image of $i_1$ or of $i_2$; the scheme $C_1 \times_{C_s} C_2$ is reduced, has exactly $n$ points, and $n > 0$; the point of $C_s$ obtained from $\varepsilon$ by base change (the image of the closed point of $\operatorname{Spec} k$ under the induced section `sectionFibrePoint`) lies in the image of $i_1$ and not in that of $i_2$; the trace of $U$ on $C_s$, i.e. the preimage of $U$ under the first projection, is exactly the complement of the image of the crossing locus $C_1 \times_{C_s} C_2 \to C_s$; the intersection of the image of $i_1$ with that trace is the connected component, inside the trace, of the $\varepsilon$-point; the intersection of the image of $i_2$ with the trace is the complement in the trace of that connected component; there is an open $W_1 \subseteq C_s$ whose underlying set is the complement of the image of $i_2$ and for which the inclusion of $i_1^{-1}W_1$ into $C_1$ followed by $i_1$ is an open immersion; and symmetrically an open $W_2$ with underlying set the complement of the image of $i_1$ such that the inclusion of $i_2^{-1}W_2$ into $C_2$ followed by $i_2$ is an open immersion.
--
--   **The splitting algebra and the two pools of blocks.** $A$ is an $R$-algebra which is finite and faithfully flat as an $R$-module. Two natural numbers $M, M'$ are given. The near pool consists of rings $B_i$ ($i \in \mathrm{Fin}\,M$), each an $R$-algebra that is finite as an $R$-module and étale over $R$, degrees $\deg i \ge 1$, $A$-algebra isomorphisms $\varphi_i \colon A \otimes_R B_i \cong A^{\deg i}$, and closed immersions $z_i \colon \operatorname{Spec} B_i \to C$ with $z_i$ followed by $c$ equal to $\operatorname{Spec}$ of the structure map $R \to B_i$; the hypotheses `hzU`, `hzdisj` require that the image of each $z_i$ lies in $U$ and that the images are pairwise disjoint, and `hzε` requires that for every algebraically closed field $k$, every $s \colon \operatorname{Spec} k \to \operatorname{Spec} R$ and every $i$, the preimage in $C_s$ of the image of $z_i$ is contained in the connected component, inside the trace of $U$ on $C_s$, of the $\varepsilon$-point of $C_s$. The far pool consists of the analogous data $B'_i$, $\deg' i \ge 1$, $\varphi'_i \colon A \otimes_R B'_i \cong A^{\deg' i}$ and closed immersions $z'_i \colon \operatorname{Spec} B'_i \to C$ over $\operatorname{Spec} R$ ($i \in \mathrm{Fin}\,M'$), with `hz'U` and `hz'disj` as before, `hzz'` requiring the image of every $z_i$ to be disjoint from the image of every $z'_j$, and `hz'ε` requiring that for every algebraically closed field $k$, every $s$ with $\operatorname{pr}_2 \colon C_s \to \operatorname{Spec} k$ not smooth and every $i$, the preimage in $C_s$ of the image of $z'_i$ lies in the trace of $U$ on $C_s$ with the connected component of the $\varepsilon$-point removed.
--
--   **Numerical data.** Natural numbers $r, r'$, an index $i_0 \in \mathrm{Fin}\,M'$ and $e$ are given with $g + e = r + r' \deg' i_0$, $2g + 1 \le r$ and $2g + 1 \le r'$; a bound $b$ with $\deg i \le b$ for all $i$ and $\deg' i \le b$ for all $i$; and the counting inequalities $(g+2)(r + r'b)b^e + e < M$ and $(g+2)(r + r'b)b^e + e + 1 < M'$.
--
--   **Conclusion.** Let $\Omega$ be an algebraically closed field which is an $R$-algebra, write $C_\Omega = C \times_{\operatorname{Spec} R} \operatorname{Spec} \Omega$ for the base change along $\operatorname{Spec}$ of $R \to \Omega$, and let $L_0$ be a module on $C_\Omega$ which is invertible (locally isomorphic to the structure sheaf) and satisfies `IsAlgEquivZero` for $\operatorname{pr}_2 \colon C_\Omega \to \operatorname{Spec}\Omega$, i.e. there are a scheme $T'$ with a locally of finite type, geometrically integral morphism $h \colon T' \to \operatorname{Spec}\Omega$, an invertible module $M$ on $C_\Omega \times_{\operatorname{Spec}\Omega} T'$ and two sections $t_0, t_1$ of $h$ such that the pullback of $M$ along the base change of $t_0$ is isomorphic to the structure sheaf and its pullback along the base change of $t_1$ is isomorphic to the pullback of $L_0$. Let further $q \colon \mathrm{Fin}(\deg' i_0) \to \{\,p \colon \operatorname{Spec}\Omega \to C_\Omega \mid p \text{ followed by } \operatorname{pr}_2 = \mathrm{id}\,\}$ be a family of $\Omega$-points of $C_\Omega$ whose underlying morphisms are pairwise distinct and such that each $q_m$, composed with the first projection, factors as $\operatorname{Spec}\psi$ followed by $z'_{i_0}$ for some $R$-algebra homomorphism $\psi \colon B'_{i_0} \to \Omega$.
--
--   Then there exist natural numbers $e_1, e_2$ with $e_1 + e_2 = e$ and injective maps $a \colon \mathrm{Fin}\,e_1 \to \mathrm{Fin}\,M$ and $a' \colon \mathrm{Fin}\,e_2 \to \mathrm{Fin}\,M'$ with $a'(j) \ne i_0$ for all $j$, such that for every choice of $\Omega$-points $v_j$ ($j \in \mathrm{Fin}\,e_1$) and $v'_j$ ($j \in \mathrm{Fin}\,e_2$) of $C_\Omega$, $v_j$ lying on the block $z_{a(j)}$ and $v'_j$ on the block $z'_{a'(j)}$ in the above factorisation sense, both of the following hold for the module
--   $$N = L_0 \otimes \Big( \big( I_\varepsilon^{\,r} \cdot \big(\textstyle\prod_m I_{q_m}\big)^{r'} \big)^{\vee} \otimes \big( \textstyle\prod_j I_{v_j} \cdot \prod_j I_{v'_j} \big) \Big),$$
--   where for an $\Omega$-point $p$ the symbol $I_p$ denotes the ideal sheaf data `ker` of $p$, products and powers are taken in the monoid of ideal sheaf data, the second factor is the dual (`invModule`) of the module attached to $I_\varepsilon^{\,r}(\prod_m I_{q_m})^{r'}$, the third is the module attached to $\prod_j I_{v_j} \cdot \prod_j I_{v'_j}$ (the module of an ideal sheaf being the kernel of the map from the structure sheaf to the pushforward of the structure sheaf of the corresponding closed subscheme), and $I_\varepsilon$ is the ideal of the $\varepsilon$-point of $C_\Omega$:
--
--   (i) for every two-chart affine open cover $\mathcal W$ of $C_\Omega$, the degree-one two-chart Čech cohomology $H^1$ of $N$ with respect to $\mathcal W$ and $\operatorname{pr}_2$ is subsingleton, i.e. vanishes;
--
--   (ii) for every morphism $\tau$ from the unit object of the monoidal category of modules on $C_\Omega$ to $N$ with $\tau \ne 0$, the support of the zero-scheme ideal `zeroSchemeIdeal` $\tau$ — the least ideal sheaf datum containing, on each affine open, the ideal generated by the coefficients of $\tau$ — is contained, as a subset of $C_\Omega$, in the preimage of $U$ under the first projection.
--
--   This is the two-sided block general position statement for a family of curves over $\operatorname{Spec} R$ all of whose geometric fibres are either smooth (hence inside $U$) or a union of two smooth proper geometrically integral curves crossing in finitely many points: after removing suitably chosen blocks from each of the two pools, the twisted bundle has vanishing two-chart Čech $H^1$ on the $\Omega$-fibre and every nonzero section of it has its zero locus inside the relatively smooth open $U$. It is the input for [`AlgebraicGeometry.RelPicard.exists_split_injective_forall_subsingleton_H1_lineBundle_and_support_subset_of_twoSidedBlocks_of_bijective_sections`](thm.html#AlgebraicGeometry.RelPicard.exists_split_injective_forall_subsingleton_H1_lineBundle_and_support_subset_of_twoSidedBlocks_of_bijective_sections) in the construction of the relative Picard scheme and the Néron model used on the modularity route.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_split_injective_forall_subsingleton_H1_and_support_subset_of_twoSidedBlocks_of_bijective_sections.lean

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

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra

open AlgebraicGeometry.SmoothProperCurve
open AlgebraicCurve

theorem AlgebraicGeometry.RelPicard.exists_split_injective_forall_subsingleton_H1_and_support_subset_of_twoSidedBlocks_of_bijective_sections
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
    (hMlt : (g + 2) * (r + r' * b) * b ^ e + e < M) (hM'lt : (g + 2) * (r + r' * b) * b ^ e + e + 1 < M') :
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra R Ω]
      (L₀ : (pullback c (SmoothProperCurve.specMap R Ω)).Modules), Scheme.Modules.IsInvertible L₀ →
      IsAlgEquivZero (pullback.snd c (SmoothProperCurve.specMap R Ω)) L₀ →

      ∀ (q : Fin (deg' i₀) → {q : Spec (CommRingCat.of Ω) ⟶ pullback c (SmoothProperCurve.specMap R Ω) //
            q ≫ pullback.snd c (SmoothProperCurve.specMap R Ω) = 𝟙 _}),
        Function.Injective (fun m => (q m).1) →
        (∀ m, ∃ ψ : B' i₀ →ₐ[R] Ω,
          (q m).1 ≫ pullback.fst c (SmoothProperCurve.specMap R Ω) = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ z' i₀) →
      ∃ (e₁ e₂ : ℕ) (_ : e₁ + e₂ = e) (a : Fin e₁ → Fin M) (a' : Fin e₂ → Fin M'),
        Function.Injective a ∧ Function.Injective a' ∧ (∀ j, a' j ≠ i₀) ∧
        ∀ (v : Fin e₁ → {q : Spec (CommRingCat.of Ω) ⟶ pullback c (SmoothProperCurve.specMap R Ω) //
            q ≫ pullback.snd c (SmoothProperCurve.specMap R Ω) = 𝟙 _})
          (v' : Fin e₂ → {q : Spec (CommRingCat.of Ω) ⟶ pullback c (SmoothProperCurve.specMap R Ω) //
            q ≫ pullback.snd c (SmoothProperCurve.specMap R Ω) = 𝟙 _}),
          (∀ j, ∃ ψ : B (a j) →ₐ[R] Ω,
            (v j).1 ≫ pullback.fst c (SmoothProperCurve.specMap R Ω) = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ z (a j)) →
          (∀ j, ∃ ψ : B' (a' j) →ₐ[R] Ω,
            (v' j).1 ≫ pullback.fst c (SmoothProperCurve.specMap R Ω) = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ z' (a' j)) →
          (∀ 𝒲 : (pullback c (SmoothProperCurve.specMap R Ω)).TwoAffineOpenCover,
            Subsingleton (𝒲.sectionsOf (pullback.snd c (SmoothProperCurve.specMap R Ω))
              (L₀ ⊗ ((((sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1.ker) ^ r * (∏ m, (q m).1.ker) ^ r').invModule ⊗
                ((∏ j, (v j).1.ker) * (∏ j, (v' j).1.ker)).module))).H1) ∧
          (∀ τ : 𝟙_ (pullback c (SmoothProperCurve.specMap R Ω)).Modules ⟶
              (L₀ ⊗ ((((sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1.ker) ^ r * (∏ m, (q m).1.ker) ^ r').invModule ⊗
                ((∏ j, (v j).1.ker) * (∏ j, (v' j).1.ker)).module)),
            τ ≠ 0 → ((Scheme.Modules.zeroSchemeIdeal τ).support : Set ↥(pullback c (SmoothProperCurve.specMap R Ω))) ⊆
              ((pullback.fst c (SmoothProperCurve.specMap R Ω)) ⁻¹ᵁ U : Set ↥(pullback c (SmoothProperCurve.specMap R Ω)))) := by sorry
