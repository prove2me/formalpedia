-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_and_support_subset_fibre_of_twoSidedBlocks_of_injective
-- name    : AlgebraicGeometry.RelPicard.exists_chart_subsingleton_H1_and_support_subset_fibre_of_twoSidedBlocks_of_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/a46a98c3-6c20-5b8a-b620-65ac396610ba
-- title:
--   Two-sided chart with vanishing H¹ and zeros inside U
-- statement:
--   Throughout, $R$ is a commutative ring and $c : C \to \operatorname{Spec} R$ is a proper flat morphism of schemes.
--
--   **Curve data.** A two-affine open cover $\mathcal V$ of $C$ is given (two affine opens $\mathcal V.U_0,\mathcal V.U_1$ with $\mathcal V.U_0\sqcup\mathcal V.U_1=\top$ and affine intersection). The hypothesis `hH0` requires that for every $R$-algebra $A$ the structure map $A \to \Gamma(C\times_{\operatorname{Spec} R}\operatorname{Spec} A,\top)$, formed from the projection to $\operatorname{Spec} A$, be bijective. Further, $\varepsilon$ is a section of $c$ (a morphism $\operatorname{Spec} R \to C$ with $\varepsilon \circ c = \mathrm{id}$), and $U \subseteq C$ is an open subscheme such that $U \hookrightarrow C \to \operatorname{Spec} R$ is smooth of relative dimension $1$, with `hεA` asserting that the image of $\varepsilon$ lies in $U$.
--
--   **Fibre hypotheses.** `hgoodU`: for every algebraically closed field $k$ and every $x : \operatorname{Spec} k \to \operatorname{Spec} R$ whose fibre $C_x \to \operatorname{Spec} k$ is smooth, the image of $C_x$ in $C$ lies in $U$. `hgred`: every such geometric fibre $C_x$ is reduced. `hg`: a natural number $g$ is fixed, and for every algebraically closed $k$, every $x$ and every two-affine open cover $\mathcal W$ of the fibre, the $k$-dimension of the Čech $H^1$ (the cokernel $M_{01}/\operatorname{im}(\delta)$ of the two-chart Čech differential) of the structure-sheaf sections of $\mathcal W$ equals $g$.
--
--   **Degeneration hypothesis `hbad`.** For every algebraically closed field $k$ and every $s : \operatorname{Spec} k \to \operatorname{Spec} R$ whose fibre is not smooth, there exist schemes $C_1,C_2$ with structure morphisms $c_1,c_2$ to $\operatorname{Spec} k$, each proper, smooth of relative dimension $1$ and geometrically integral, closed immersions $i_1 : C_1 \to C_s$, $i_2 : C_2 \to C_s$ over $\operatorname{Spec} k$, and $n \in \mathbb N$, such that: the images of $i_1$ and $i_2$ cover $C_s$; $C_1\times_{C_s}C_2$ is reduced with exactly $n$ points and $n>0$; the point of $C_s$ determined by $\varepsilon$ and the closed point of $\operatorname{Spec} k$ lies in $\operatorname{im} i_1 \setminus \operatorname{im} i_2$; the preimage of $U$ in $C_s$ is the complement of the image of $C_1\times_{C_s}C_2 \to C_1 \to C_s$; $\operatorname{im} i_1$ meets that preimage exactly in the connected component of the marked point inside it, while $\operatorname{im} i_2$ meets it exactly in the complement of that component; and there are opens $W_1, W_2$ of $C_s$ with underlying sets $(\operatorname{im} i_2)^c$ and $(\operatorname{im} i_1)^c$ such that the restriction of $i_1$ to $i_1^{-1}W_1$, respectively of $i_2$ to $i_2^{-1}W_2$, is an open immersion.
--
--   **Blocks over $A$.** $A$ is a Noetherian $R$-algebra. Two finite pools of $R$-algebras are given: $B_i$ for $i \in \mathrm{Fin}\,M$ (the near pool) and $B'_i$ for $i \in \mathrm{Fin}\,M'$ (the far pool), with degrees $\deg i \ge 1$, $\deg' i \ge 1$ and $A$-algebra isomorphisms $\varphi_i : A\otimes_R B_i \cong A^{\deg i}$, $\varphi'_i : A\otimes_R B'_i \cong A^{\deg' i}$. Closed immersions $z_i : \operatorname{Spec} B_i \to C$ and $z'_i : \operatorname{Spec} B'_i \to C$ are given, compatible with the structure morphisms (`hz`, `hz'`: $z_i$ followed by $c$ is $\operatorname{Spec}$ of $R\to B_i$, and likewise for $z'_i$), with images contained in $U$ (`hzU`, `hz'U`), pairwise disjoint images within each pool (`hzdisj`, `hz'disj`) and disjoint images across the two pools (`hzz'`). Positional hypotheses: `hzε` requires that for every algebraically closed $k$, every $s : \operatorname{Spec} k \to \operatorname{Spec} R$ and every near index $i$, the preimage in $C_s$ of $\operatorname{im} z_i$ lies in the connected component, inside the preimage of $U$, of the point marked by $\varepsilon$; `hz'ε` requires that for every algebraically closed $k$, every $s$ with non-smooth fibre and every far index $i$, the preimage in $C_s$ of $\operatorname{im} z'_i$ lies in the preimage of $U$ minus that connected component.
--
--   **Sections.** For each near index $i$ a family $\sigma_{i,\bullet}$ of $\deg i$ sections of the base change $C_A := C\times_{\operatorname{Spec} R}\operatorname{Spec} A \to \operatorname{Spec} A$ is given, and for each far index $i$ a family $\sigma'_{i,\bullet}$ of $\deg' i$ such sections. Each $\sigma_{i,m}$, composed with $C_A \to C$, factors through $z_i$ (`hσfac`), and each $\sigma'_{i,m}$ factors through $z'_i$ (`hσ'fac`); the families are injective in the section index (`hσinj`, `hσ'inj`).
--
--   **Numerical data.** Natural numbers $r, r'$, a distinguished far index $i_0$, and $e, \rho$ with $\rho = r + r'\deg' i_0$, $g + e = \rho$, $2g+1 \le r$ and $2g+1 \le r'$.
--
--   **Twist block over $A$.** A closed immersion $z_A : \operatorname{Spec}(A\otimes_R B'_{i_0}) \to C_A\times_{\operatorname{Spec} A}\operatorname{Spec} A$ is given such that $z_A$ followed by the two first projections down to $C$ equals $\operatorname{Spec}$ of the inclusion $B'_{i_0} \to A \otimes_R B'_{i_0}$ followed by $z'_{i_0}$ (`hzA`), and $z_A$ followed by the second projection equals $\operatorname{Spec}$ of $A \to A\otimes_R B'_{i_0}$ (`hzA'`).
--
--   **Polarising divisor.** $E$ is a relative effective Cartier divisor of degree $\rho$ on $C_A$ over $\mathrm{id}_{\operatorname{Spec} A}$, that is, an ideal sheaf datum whose associated closed subscheme is finite, flat and locally of finite presentation over $\operatorname{Spec} A$ with fibre rank $\rho$ at every point; its ideal is pinned by `hEI` to be $I_{\varepsilon_A}^{\,r}\cdot (\ker z_A)^{r'}$, where $I_{\varepsilon_A}$ is the kernel ideal of the rigidifying section attached to the base-changed section $\varepsilon_A$; and `hEU` requires the support of $E$'s ideal to lie in the preimage of $U$ under $C_A \to C$.
--
--   **Chart divisors.** A type $\iota$ and an indexing map `idx` are given, assigning an element of $\iota$ to each tuple consisting of a splitting $e_1 + e_2 = e$, an injective $a : \mathrm{Fin}\,e_1 \to \mathrm{Fin}\,M$, an injective $a' : \mathrm{Fin}\,e_2 \to \mathrm{Fin}\,M'$, and choices $m$, $m'$ of a section index for every near, respectively far, block. For each $i \in \iota$, $D_{\gamma}(i)$ is a relative effective Cartier divisor of degree $e$ on $C_A$ over $\mathrm{id}_{\operatorname{Spec} A}$, with `hDγI` requiring that the ideal of $D_\gamma(\mathrm{idx}\,e_1\,e_2\,\cdot\,a\,a'\,m\,m')$ be the product of the product over $j \in \mathrm{Fin}\,e_1$ of the graph ideals of the sections $\sigma_{a(j),\,m(a(j))}$ with the product over $j \in \mathrm{Fin}\,e_2$ of the graph ideals of the sections $\sigma'_{a'(j),\,m'(a'(j))}$, and `hDγU` requiring each $D_\gamma(i)$ to be supported in the preimage of $U$.
--
--   **Counting hypotheses.** A bound $b$ with $\deg i \le b$ and $\deg' i \le b$ for all $i$, and the two inequalities $(g+2)(r + r'b)b^{\,e} + e < M$ and $(g+2)(r + r'b)b^{\,e} + e + 1 < M'$.
--
--   **Conclusion.** For every scheme $T$, every $t : T \to \operatorname{Spec} A$ and every rigidified line bundle $L$ on $C_A\times_{\operatorname{Spec} A} T$ relative to $\varepsilon_A$ (an invertible module $L.L$ together with a trivialisation of its pullback along the rigidifying section) satisfying `FibrewiseAlgEquivZero`, that is, such that for every algebraically closed field $k$ and every $k$-point $s$ of $T$ the restriction of $L.L$ to the fibre satisfies `IsAlgEquivZero` (there exist a locally finite type, geometrically integral $T' \to \operatorname{Spec} k$, an invertible module $M$ on the fibre product and two $k$-points $t_0, t_1$ of $T'$ whose associated pullbacks of $M$ are isomorphic to the unit module and to the pullback of the fibre of $L.L$ respectively), and for every field $k$ — here not assumed algebraically closed — and every $s : \operatorname{Spec} k \to T$, there exists an index $i \in \iota$ with the following two properties, where $N$ denotes the module $L.L \otimes \bigl(\mathcal O(E_t) \otimes I(D_\gamma(i)_t)\bigr)$, formed from the pullbacks of $E$ and $D_\gamma(i)$ along $t$, with $\mathcal O(E_t)$ the dual of the ideal module of $E_t$ and $I(D_\gamma(i)_t)$ the ideal module of $D_\gamma(i)_t$:
--
--   First, for every two-affine open cover $\mathcal W$ of the fibre of $C_A\times_{\operatorname{Spec} A} T$ at $s$, the Čech $H^1$ of the $\mathcal W$-sections of the fibre of $N$ at $s$ (the restriction of $N$ along the first projection) is a subsingleton.
--
--   Second, for every morphism $\tau$ from the unit module on $C_A\times_{\operatorname{Spec} A,\, s\circ t} \operatorname{Spec} k$ to the pullback of $N$ along the morphism induced by $s$, if $\tau \ne 0$ then the support of the zero-scheme ideal of $\tau$ (the infimum of the ideal sheaf data dominating the coefficient ideals of $\tau$ on affine opens) is contained in the preimage of the preimage of $U$, i.e. in the open set obtained by pulling $U$ back along $C_A \to C$ and then along the first projection from the fibre product over $s \circ t$.
--
--   This is the chart-supplying step for the $\mathrm{Pic}^0$ cut of the relative Picard functor of a proper flat curve with a section, in the two-sided form adapted to fibres degenerating into two smooth geometrically integral curves meeting in finitely many points: from a near pool of blocks concentrated in the component of the marked section and a far pool concentrated away from it, together with a polarising divisor $E$ of degree $\rho = r + r'\deg' i_0$, it produces for each field-valued point of the parameter scheme a degree-$e$ chart divisor $D_\gamma$ such that $L(E - D_\gamma)$ has vanishing Čech $H^1$ on the fibre and all of whose nonzero sections vanish only inside the relative smooth locus $U$. It is used by the construction of representing charts for the algebraic-equivalence-zero cut of the relative Picard functor after base change away from the smooth locus.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_and_support_subset_fibre_of_twoSidedBlocks_of_injective.lean

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

theorem AlgebraicGeometry.RelPicard.exists_chart_subsingleton_H1_and_support_subset_fibre_of_twoSidedBlocks_of_injective
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
    (A : Type u) [CommRing A] [Algebra R A] [IsNoetherianRing A]

    {M M' : ℕ} (B : Fin M → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    (B' : Fin M' → Type u) [∀ i, CommRing (B' i)] [∀ i, Algebra R (B' i)]
    (deg : Fin M → ℕ) (hdeg : ∀ i, 1 ≤ deg i) (φ : ∀ i, TensorProduct R A (B i) ≃ₐ[A] (Fin (deg i) → A))
    (deg' : Fin M' → ℕ) (hdeg' : ∀ i, 1 ≤ deg' i) (φ' : ∀ i, TensorProduct R A (B' i) ≃ₐ[A] (Fin (deg' i) → A))
    (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ C) [∀ i, IsClosedImmersion (z i)]
    (z' : ∀ i, Spec (CommRingCat.of (B' i)) ⟶ C) [∀ i, IsClosedImmersion (z' i)]
    (hz : ∀ i, z i ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R (B i))))
    (hz' : ∀ i, z' i ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R (B' i))))
    (hzU : ∀ i, Set.range (z i).base ⊆ (U : Set C)) (hz'U : ∀ i, Set.range (z' i).base ⊆ (U : Set C))
    (hzdisj : Pairwise fun i j => Disjoint (Set.range (z i).base) (Set.range (z j).base))
    (hz'disj : Pairwise fun i j => Disjoint (Set.range (z' i).base) (Set.range (z' j).base))
    (hzz' : ∀ i j, Disjoint (Set.range (z i).base) (Set.range (z' j).base))
    (hzε : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) (i : Fin M),
      (pullback.fst c s).base ⁻¹' Set.range (z i).base ⊆
        connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s))
          (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k)))
    (hz'ε : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) (i : Fin M'),
      ¬ Smooth (pullback.snd c s) →
      (pullback.fst c s).base ⁻¹' Set.range (z' i).base ⊆
        ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) \
          connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s))
            (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k)))

    (σ : ∀ i, Fin (deg i) → SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (baseChange R c A))
    (σ' : ∀ i, Fin (deg' i) → SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (baseChange R c A))
    (hσfac : ∀ i m, ∃ y : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of (B i)),
      (σ i m).1 ≫ pullback.fst c (specMap R A) = y ≫ z i)
    (hσ'fac : ∀ i m, ∃ y : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of (B' i)),
      (σ' i m).1 ≫ pullback.fst c (specMap R A) = y ≫ z' i)
    (hσinj : ∀ i, Function.Injective (σ i)) (hσ'inj : ∀ i, Function.Injective (σ' i))

    (r r' : ℕ) (i₀ : Fin M') (e ρ : ℕ) (hρ : ρ = r + r' * deg' i₀) (he : g + e = ρ)
    (hr : 2 * g + 1 ≤ r) (hr' : 2 * g + 1 ≤ r')

    (zA : Spec (CommRingCat.of (TensorProduct R A (B' i₀))) ⟶ pullback (baseChange R c A) (𝟙 (Spec (CommRingCat.of A))))
    [IsClosedImmersion zA]
    (hzA : zA ≫ pullback.fst (baseChange R c A) (𝟙 (Spec (CommRingCat.of A))) ≫ pullback.fst c (specMap R A) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B' i₀)).toRingHom) ≫ z' i₀)
    (hzA' : zA ≫ pullback.snd (baseChange R c A) (𝟙 (Spec (CommRingCat.of A))) =
      Spec.map (CommRingCat.ofHom (algebraMap A (TensorProduct R A (B' i₀)))))

    (E : RelEffCartierDiv (baseChange R c A) ρ (𝟙 (Spec (CommRingCat.of A))))
    (hEI : E.I = (sectionIdeal (baseChange R c A) (sectionBaseChange A ε) (𝟙 (Spec (CommRingCat.of A)))) ^ r * zA.ker ^ r')
    (hEU : E.SupportedIn (pullback.fst c (specMap R A) ⁻¹ᵁ U))

    {ι : Type u}
    (idx : ∀ (e₁ e₂ : ℕ), e₁ + e₂ = e → {a : Fin e₁ → Fin M // Function.Injective a} →
      {a' : Fin e₂ → Fin M' // Function.Injective a'} → (∀ i, Fin (deg i)) → (∀ i, Fin (deg' i)) → ι)
    (Dγ : ι → RelEffCartierDiv (baseChange R c A) e (𝟙 (Spec (CommRingCat.of A))))
    (hDγI : ∀ (e₁ e₂ : ℕ) (he₁₂ : e₁ + e₂ = e) (a : {a : Fin e₁ → Fin M // Function.Injective a})
      (a' : {a' : Fin e₂ → Fin M' // Function.Injective a'}) (m : ∀ i, Fin (deg i)) (m' : ∀ i, Fin (deg' i)),
      (Dγ (idx e₁ e₂ he₁₂ a a' m m')).I =
        prodKerGraph (baseChange R c A) (fun j => (σ (a.1 j) (m (a.1 j))).1) (fun j => (σ (a.1 j) (m (a.1 j))).2) *
        prodKerGraph (baseChange R c A) (fun j => (σ' (a'.1 j) (m' (a'.1 j))).1) (fun j => (σ' (a'.1 j) (m' (a'.1 j))).2))
    (hDγU : ∀ i, (Dγ i).SupportedIn (pullback.fst c (specMap R A) ⁻¹ᵁ U))
    (b : ℕ) (hdegb : ∀ i, deg i ≤ b) (hdeg'b : ∀ i, deg' i ≤ b)
    (hMlt : (g + 2) * (r + r' * b) * b ^ e + e < M) (hM'lt : (g + 2) * (r + r' * b) * b ^ e + e + 1 < M') :
    ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of A)) (L : RigidifiedLineBundle (baseChange R c A) (sectionBaseChange A ε) t),
      FibrewiseAlgEquivZero L → ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T),
      ∃ i : ι,
        (∀ (𝒲 : (pullback (pullback.snd (baseChange R c A) t) s).TwoAffineOpenCover),
          Subsingleton (𝒲.sectionsOf (fibreAt (baseChange R c A) t s) (fibreModule (baseChange R c A) t s
            (L.L ⊗ ((E.pullbackAlong t (Category.comp_id t)).lineBundle ⊗ ((Dγ i).pullbackAlong t (Category.comp_id t)).idealModule)))).H1) ∧
        (∀ τ : 𝟙_ (pullback (baseChange R c A) (s ≫ t)).Modules ⟶ (Scheme.Modules.pullback (mapOnProdOver (baseChange R c A) s rfl)).obj
            (L.L ⊗ ((E.pullbackAlong t (Category.comp_id t)).lineBundle ⊗ ((Dγ i).pullbackAlong t (Category.comp_id t)).idealModule)),
          τ ≠ 0 → ((Scheme.Modules.zeroSchemeIdeal τ).support : Set ↥(pullback (baseChange R c A) (s ≫ t))) ⊆
            ((pullback.fst (baseChange R c A) (s ≫ t)) ⁻¹ᵁ (pullback.fst c (specMap R A) ⁻¹ᵁ U) :
              Set ↥(pullback (baseChange R c A) (s ≫ t)))) := by sorry
