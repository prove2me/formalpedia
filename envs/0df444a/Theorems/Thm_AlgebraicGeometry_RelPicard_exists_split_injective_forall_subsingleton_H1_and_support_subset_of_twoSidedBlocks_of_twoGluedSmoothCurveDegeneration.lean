-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_split_injective_forall_subsingleton_H1_and_support_subset_of_twoSidedBlocks_of_twoGluedSmoothCurveDegeneration
-- name    : AlgebraicGeometry.RelPicard.exists_split_injective_forall_subsingleton_H1_and_support_subset_of_twoSidedBlocks_of_twoGluedSmoothCurveDegeneration
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/40d0a581-7c0a-5c30-b010-634226722ca3
-- title:
--   Two-sided block general position at a two-component degenerate fibre
-- statement:
--   Throughout, $R$ is a commutative ring, $c\colon C\to\operatorname{Spec}R$ is proper, and $\varepsilon$ is a section of $c$, i.e. a morphism $\operatorname{Spec}R\to C$ whose composite with $c$ is the identity. An open subscheme $U\subseteq C$ is given such that the composite of the inclusion $U.\iota$ with $c$ is smooth of relative dimension $1$, and the hypothesis `hεU` requires the image of $\varepsilon$ to lie in $U$.
--
--   **Block data.** Two finite pools of $R$-points are given: natural numbers $M,M'$, families of $R$-algebras $B_i$ ($i\in\mathrm{Fin}\,M$) and $B'_i$ ($i\in\mathrm{Fin}\,M'$), morphisms $z_i\colon\operatorname{Spec}B_i\to C$ and $z'_i\colon\operatorname{Spec}B'_i\to C$, the hypotheses `hz` and `hz'` asserting that these are morphisms over $\operatorname{Spec}R$ (composition with $c$ is $\operatorname{Spec}$ of the structure map), `hzU` and `hz'U` that all their images lie in $U$, and `hzdisj`, `hz'disj`, `hzz'` that the images are pairwise disjoint inside each pool and between the two pools. Degree functions $\deg\colon\mathrm{Fin}\,M\to\mathbb N$ and $\deg'\colon\mathrm{Fin}\,M'\to\mathbb N$ are given with $\deg i\ge 1$, $\deg' i\ge 1$ (`hdeg`, `hdeg'`) and $\deg i\le b$, $\deg' i\le b$ for a bound $b$ (`hdegb`, `hdeg'b`).
--
--   **Numerical data.** Natural numbers $g,r,r',e$ and an index $i_0\in\mathrm{Fin}\,M'$ satisfy $2g+1\le r$, $2g+1\le r'$ (`hr`, `hr'`), $g+e=r+r'\deg'(i_0)$ (`he`), and the counting bounds $(g+2)(r+r'b)\,b^{e}+e<M$ (`hcount`) and $(g+2)(r+r'b)\,b^{e}+e+1<M'$ (`hcount'`).
--
--   **The geometric fibre.** $\Omega$ is an algebraically closed field and an $R$-algebra; write $X=C\times_{\operatorname{Spec}R}\operatorname{Spec}\Omega$ with projections $p=\mathrm{pullback.fst}$ to $C$ and $\pi=\mathrm{pullback.snd}$ to $\operatorname{Spec}\Omega$, and $U_\Omega=p^{-1}(U)$. The bijections `eB i` and `eB' i` identify the set of $R$-algebra maps $B_i\to\Omega$ with $\mathrm{Fin}(\deg i)$, and those of $B'_i\to\Omega$ with $\mathrm{Fin}(\deg' i)$. It is assumed that $\pi$ is proper, that $X$ is reduced, and (`hns`) that $\pi$ is **not** smooth. A two-affine open cover $\mathcal W_0$ of $X$ is given; a two-affine open cover consists of two affine opens whose union is $X$ and whose intersection is affine. Finally $q\colon\mathrm{Fin}(\deg' i_0)\to\{\,\Omega\text{-points of }X\,\}$ is a family of sections of $\pi$, and `hq` says that $q_m$ followed by $p$ equals $\operatorname{Spec}$ of the $R$-algebra map $(\mathrm{eB}'_{i_0})^{-1}(m)$ followed by $z'_{i_0}$; thus the $q_m$ enumerate the $\Omega$-points of the block $z'_{i_0}$.
--
--   **The degeneration hypothesis `hbad`.** For every algebraically closed field $k$ and every morphism $s\colon\operatorname{Spec}k\to\operatorname{Spec}R$ for which $\mathrm{pullback.snd}\,c\,s$ fails to be smooth, there exist two schemes $C_1,C_2$ proper, smooth of relative dimension $1$ and geometrically integral over $k$, closed immersions $i_1,i_2$ of $C_1,C_2$ into $C\times_{\operatorname{Spec}R}\operatorname{Spec}k$ over the structure morphisms, and a natural number $n$, such that: the images of $i_1$ and $i_2$ cover all points of the fibre; $\operatorname{pullback}i_1\,i_2$ is reduced with $\mathrm{Nat.card}=n$ and $n>0$; the image of the closed point of $\operatorname{Spec}k$ under the section `sectionFibrePoint ε s` lies in the image of $i_1$ and not in that of $i_2$; the underlying set of the preimage of $U$ is exactly the complement of the image of the crossing locus, i.e. of $\mathrm{pullback.fst}\,i_1\,i_2$ followed by $i_1$; the intersection of the image of $i_1$ with that preimage is the connected component of the section point inside it, and the intersection of the image of $i_2$ with the preimage is the complement of that connected component in the preimage; and there are opens $W_1$, $W_2$ of the fibre whose underlying sets are the complements of the images of $i_2$, respectively $i_1$, such that the inclusion of $i_1^{-1}W_1$ followed by $i_1$, respectively of $i_2^{-1}W_2$ followed by $i_2$, is an open immersion.
--
--   **Position of the two pools at the fibre over $\Omega$.** The hypothesis `hzε` requires, for every $i$, that $p^{-1}(\operatorname{im}z_i)$ be contained in the connected component of the point $\varepsilon_\Omega$ of `sectionFibrePoint ε (specMap R Ω)` inside $U_\Omega$; `hz'ε` requires, for every $i$, that $p^{-1}(\operatorname{im}z'_i)$ be contained in $U_\Omega$ minus that connected component.
--
--   **Cohomology of the structure sheaf and the line bundle.** For a two-affine open cover $\mathcal W$ of $X$ and a module $N$ on $X$, `𝒲.sectionsOf π N` is the two-term Čech complex of $N$ over the cover, with $\Omega$-modules of sections on the two charts and on their intersection, and $H^0$, $H^1$ the kernel and the cokernel of the difference of the two restriction maps. The hypotheses `hH0` and `hg` require that for every two-affine open cover $\mathcal W$ of $X$ one has $\dim_\Omega H^0=1$ and $\dim_\Omega H^1=g$ for the unit module (structure sheaf). Finally, $L_0$ is a module on $X$ which is invertible (`hL₀`) and satisfies `IsAlgEquivZero π L₀` (`h0`): there exist a scheme $T'$ locally of finite type and geometrically integral over $\operatorname{Spec}\Omega$, an invertible module $N$ on $X\times_{\operatorname{Spec}\Omega}T'$ and two sections $t_0,t_1$ of $T'\to\operatorname{Spec}\Omega$, such that the pullback of $N$ along the base change by $t_0$ is isomorphic to the structure sheaf of $X\times_{\operatorname{Spec}\Omega}\operatorname{Spec}\Omega$, and its pullback along the base change by $t_1$ is isomorphic to the pullback of $L_0$ along the first projection of that same pullback.
--
--   **Conclusion.** There exist natural numbers $e_1,e_2$ with $e_1+e_2=e$ and injective maps $a\colon\mathrm{Fin}\,e_1\to\mathrm{Fin}\,M$, $a'\colon\mathrm{Fin}\,e_2\to\mathrm{Fin}\,M'$ with $a'(j)\neq i_0$ for all $j$, such that the following holds for *every* choice of families $v\colon\mathrm{Fin}\,e_1\to\{\Omega\text{-points of }X\}$ and $v'\colon\mathrm{Fin}\,e_2\to\{\Omega\text{-points of }X\}$ (sections of $\pi$) such that each $v_j$ lies over the chosen block $z_{a(j)}$ — there is an $R$-algebra map $\psi\colon B_{a(j)}\to\Omega$ with $v_j$ followed by $p$ equal to $\operatorname{Spec}\psi$ followed by $z_{a(j)}$ — and each $v'_j$ lies over $z'_{a'(j)}$ in the same sense. Writing $\mathcal L$ for the module
--   $$\mathcal L=L_0\otimes\Big(\big(\ker(\varepsilon_\Omega)^{\,r}\cdot\big(\textstyle\prod_m\ker q_m\big)^{r'}\big)^{\mathrm{inv}}\otimes\big(\textstyle\prod_j\ker v_j\cdot\prod_j\ker v'_j\big)^{\mathrm{mod}}\Big),$$
--   where for an ideal sheaf datum $I$ on $X$ the module $I^{\mathrm{mod}}$ is the kernel of the map from the unit module to the pushforward of the unit module along the inclusion of the associated closed subscheme, $I^{\mathrm{inv}}$ is its dual, the kernels are the kernel ideal sheaf data of the indicated $\Omega$-points, and products and powers are products of ideal sheaf data, the two assertions are:
--
--   1. for every two-affine open cover $\mathcal W$ of $X$, the Čech $H^1$ of $\mathcal L$ over $\mathcal W$ (with respect to $\pi$) is a subsingleton;
--
--   2. for every morphism $\sigma$ from the unit module of $X$ to $\mathcal L$ with $\sigma\neq 0$, the support of `Scheme.Modules.zeroSchemeIdeal σ` — the infimum of the ideal sheaf data whose ideal on each affine open contains the ideal generated by the coefficients of $\sigma$ there — is contained, as a subset of $X$, in $U_\Omega=p^{-1}(U)$.
--
--   This is the degenerate-fibre case of two-sided block general position for the relative Picard construction: at a geometric fibre that is a union of two smooth proper geometrically integral curves meeting transversally, with the section on the first component and the far pool on the second, blocks can be selected so that the twisted bundle $L_0\otimes\mathcal O(r\varepsilon+r'\sum_m q_m-\sum_j v_j-\sum_j v'_j)$ has vanishing first Čech cohomology and all of its nonzero global sections vanish only inside the smooth relative-dimension-one locus $U$. It feeds the version with bijective sections, [`AlgebraicGeometry.RelPicard.exists_split_injective_forall_subsingleton_H1_and_support_subset_of_twoSidedBlocks_of_bijective_sections`](thm.html#AlgebraicGeometry.RelPicard.exists_split_injective_forall_subsingleton_H1_and_support_subset_of_twoSidedBlocks_of_bijective_sections), and rests on the corresponding near-block and far-block selection results together with the Mayer–Vietoris comparison for two glued curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_split_injective_forall_subsingleton_H1_and_support_subset_of_twoSidedBlocks_of_twoGluedSmoothCurveDegeneration.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra MonoidalCategory
  AlgebraicGeometry.SmoothProperCurve TensorProduct

theorem AlgebraicGeometry.RelPicard.exists_split_injective_forall_subsingleton_H1_and_support_subset_of_twoSidedBlocks_of_twoGluedSmoothCurveDegeneration
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (hεU : Set.range ε.1 ⊆ (U : Set C))

    {M M' : ℕ} (B : Fin M → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    (B' : Fin M' → Type u) [∀ i, CommRing (B' i)] [∀ i, Algebra R (B' i)]
    (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ C) (z' : ∀ i, Spec (CommRingCat.of (B' i)) ⟶ C)
    (hz : ∀ i, z i ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R (B i))))
    (hz' : ∀ i, z' i ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R (B' i))))
    (hzU : ∀ i, Set.range (z i).base ⊆ (U : Set C)) (hz'U : ∀ i, Set.range (z' i).base ⊆ (U : Set C))
    (hzdisj : Pairwise fun i j => Disjoint (Set.range (z i).base) (Set.range (z j).base))
    (hz'disj : Pairwise fun i j => Disjoint (Set.range (z' i).base) (Set.range (z' j).base))
    (hzz' : ∀ i j, Disjoint (Set.range (z i).base) (Set.range (z' j).base))
    (deg : Fin M → ℕ) (hdeg : ∀ i, 1 ≤ deg i) (deg' : Fin M' → ℕ) (hdeg' : ∀ i, 1 ≤ deg' i)
    {b : ℕ} (hdegb : ∀ i, deg i ≤ b) (hdeg'b : ∀ i, deg' i ≤ b)

    (g r r' e : ℕ) (i₀ : Fin M') (hr : 2 * g + 1 ≤ r) (hr' : 2 * g + 1 ≤ r') (he : g + e = r + r' * deg' i₀)
    (hcount : (g + 2) * (r + r' * b) * b ^ e + e < M) (hcount' : (g + 2) * (r + r' * b) * b ^ e + e + 1 < M')

    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra R Ω]
    (eB : ∀ i, (B i →ₐ[R] Ω) ≃ Fin (deg i)) (eB' : ∀ i, (B' i →ₐ[R] Ω) ≃ Fin (deg' i))
    [IsProper (pullback.snd c (SmoothProperCurve.specMap R Ω))]
    [IsReduced (pullback c (SmoothProperCurve.specMap R Ω))]
    (hns : ¬ Smooth (pullback.snd c (SmoothProperCurve.specMap R Ω)))

    (𝒲₀ : (pullback c (SmoothProperCurve.specMap R Ω)).TwoAffineOpenCover)

    (q : Fin (deg' i₀) → {p : Spec (CommRingCat.of Ω) ⟶ pullback c (SmoothProperCurve.specMap R Ω) //
        p ≫ pullback.snd c (SmoothProperCurve.specMap R Ω) = 𝟙 _})
    (hq : ∀ m, (q m).1 ≫ pullback.fst c (SmoothProperCurve.specMap R Ω) =
      Spec.map (CommRingCat.ofHom ((eB' i₀).symm m).toRingHom) ≫ z' i₀)

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

    (hzε : ∀ i, (pullback.fst c (SmoothProperCurve.specMap R Ω)).base ⁻¹' Set.range (z i).base ⊆
      connectedComponentIn (((pullback.fst c (SmoothProperCurve.specMap R Ω)) ⁻¹ᵁ U : (pullback c (SmoothProperCurve.specMap R Ω)).Opens) : Set ↥(pullback c (SmoothProperCurve.specMap R Ω)))
        (((sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1).base (IsLocalRing.closedPoint Ω)))
    (hz'ε : ∀ i, (pullback.fst c (SmoothProperCurve.specMap R Ω)).base ⁻¹' Set.range (z' i).base ⊆
      (((pullback.fst c (SmoothProperCurve.specMap R Ω)) ⁻¹ᵁ U : (pullback c (SmoothProperCurve.specMap R Ω)).Opens) : Set ↥(pullback c (SmoothProperCurve.specMap R Ω))) \
        connectedComponentIn (((pullback.fst c (SmoothProperCurve.specMap R Ω)) ⁻¹ᵁ U : (pullback c (SmoothProperCurve.specMap R Ω)).Opens) : Set ↥(pullback c (SmoothProperCurve.specMap R Ω)))
          (((sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1).base (IsLocalRing.closedPoint Ω)))

    (hH0 : ∀ 𝒲 : (pullback c (SmoothProperCurve.specMap R Ω)).TwoAffineOpenCover,
      Module.finrank Ω ↥(𝒲.sectionsOf (pullback.snd c (SmoothProperCurve.specMap R Ω))
        (SheafOfModules.unit (pullback c (SmoothProperCurve.specMap R Ω)).ringCatSheaf)).H0 = 1)
    (hg : ∀ 𝒲 : (pullback c (SmoothProperCurve.specMap R Ω)).TwoAffineOpenCover,
      Module.finrank Ω (𝒲.sectionsOf (pullback.snd c (SmoothProperCurve.specMap R Ω))
        (SheafOfModules.unit (pullback c (SmoothProperCurve.specMap R Ω)).ringCatSheaf)).H1 = g)
    (L₀ : (pullback c (SmoothProperCurve.specMap R Ω)).Modules) (hL₀ : Scheme.Modules.IsInvertible L₀)
    (h0 : IsAlgEquivZero (pullback.snd c (SmoothProperCurve.specMap R Ω)) L₀) :
    ∃ (e₁ e₂ : ℕ) (_ : e₁ + e₂ = e) (a : Fin e₁ → Fin M) (a' : Fin e₂ → Fin M'),
      Function.Injective a ∧ Function.Injective a' ∧ (∀ j, a' j ≠ i₀) ∧
      ∀ (v : Fin e₁ → {p : Spec (CommRingCat.of Ω) ⟶ pullback c (SmoothProperCurve.specMap R Ω) //
          p ≫ pullback.snd c (SmoothProperCurve.specMap R Ω) = 𝟙 _})
        (v' : Fin e₂ → {p : Spec (CommRingCat.of Ω) ⟶ pullback c (SmoothProperCurve.specMap R Ω) //
          p ≫ pullback.snd c (SmoothProperCurve.specMap R Ω) = 𝟙 _}),
        (∀ j, ∃ ψ : B (a j) →ₐ[R] Ω,
          (v j).1 ≫ pullback.fst c (SmoothProperCurve.specMap R Ω) = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ z (a j)) →
        (∀ j, ∃ ψ : B' (a' j) →ₐ[R] Ω,
          (v' j).1 ≫ pullback.fst c (SmoothProperCurve.specMap R Ω) = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ z' (a' j)) →

        (∀ 𝒲 : (pullback c (SmoothProperCurve.specMap R Ω)).TwoAffineOpenCover,
          Subsingleton (𝒲.sectionsOf (pullback.snd c (SmoothProperCurve.specMap R Ω))
            (L₀ ⊗ ((((sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1.ker) ^ r * (∏ m, (q m).1.ker) ^ r').invModule ⊗
            ((∏ j, (v j).1.ker) * (∏ j, (v' j).1.ker)).module))).H1) ∧
        (∀ σ : 𝟙_ (pullback c (SmoothProperCurve.specMap R Ω)).Modules ⟶
            (L₀ ⊗ ((((sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1.ker) ^ r * (∏ m, (q m).1.ker) ^ r').invModule ⊗
            ((∏ j, (v j).1.ker) * (∏ j, (v' j).1.ker)).module)),
          σ ≠ 0 →
          ((Scheme.Modules.zeroSchemeIdeal σ).support : Set ↥(pullback c (SmoothProperCurve.specMap R Ω))) ⊆
            (((pullback.fst c (SmoothProperCurve.specMap R Ω)) ⁻¹ᵁ U : (pullback c (SmoothProperCurve.specMap R Ω)).Opens) :
              Set ↥(pullback c (SmoothProperCurve.specMap R Ω)))) := by sorry
