-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_nonempty_lineBundle_pullbackAlong_iso_invModule_pow_ker_mul_pow_prod_ker
-- name    : AlgebraicGeometry.RelEffCartierDiv.nonempty_lineBundle_pullbackAlong_iso_invModule_pow_ker_mul_pow_prod_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/b388d9b1-6ba6-5ed4-a7c1-4abc41317088
-- title:
--   Geometric fibre of 𝒪(rε+r'W) in point-ideal form
-- statement:
--   Let $R$ be a commutative ring, $C$ a scheme and $c \colon C \to \operatorname{Spec} R$ a separated morphism, and let $\varepsilon$ be a section of $c$, i.e. a morphism $\operatorname{Spec} R \to C$ with $\varepsilon \circ c$ the identity. Let $\rho, r, r', d$ be natural numbers and let $E$ be a relative effective Cartier divisor of degree $\rho$ for $c$ over the identity of $\operatorname{Spec} R$: an ideal sheaf datum $E.I$ on $C \times_{\operatorname{Spec} R} \operatorname{Spec} R$ whose closed subscheme is finite, flat and locally of finite presentation over the base via the second projection, with fibrewise rank $\rho$ at every point. Let $w \colon W \to C \times_{\operatorname{Spec} R} \operatorname{Spec} R$ be a closed immersion such that $w$ followed by the second projection is finite, flat and étale, and assume $E.I = (\mathrm{sectionIdeal}\, c\, \varepsilon)^r \cdot (\ker w)^{r'}$, where $\mathrm{sectionIdeal}$ is the kernel ideal sheaf of the rigidifying section $\mathrm{rigSection}\, c\, (\mathbb 1)\, \varepsilon$ determined by $\varepsilon$. Let $\Omega$ be an algebraically closed field and $s \colon \operatorname{Spec} \Omega \to \operatorname{Spec} R$ a geometric point. Let $q \colon \mathrm{Fin}\, d \to$ (sections of the second projection $C \times_{\operatorname{Spec} R} \operatorname{Spec}\Omega \to \operatorname{Spec}\Omega$) be such that $m \mapsto (q\,m).1$ is injective, each $(q\,m).1$, composed with the comparison map $\mathrm{mapOnProdOver}\, c\, s$ to $C \times_{\operatorname{Spec} R}\operatorname{Spec} R$, factors through $w$, and every $\Omega$-point $y$ of $W$ lying over $s$ arises in this way from some $m$; thus $q$ enumerates the $\Omega$-points of $W$ over $s$ without repetition. Let $p_\varepsilon$ be a section of the same projection with $p_\varepsilon$ followed by the first projection equal to $\varepsilon$ composed after $s$. Then there exists an isomorphism, in the modules on $C \times_{\operatorname{Spec} R} \operatorname{Spec}\Omega$, between the line bundle of the divisor obtained from $E$ by pullback along $s$ — that is, the dual of the module of the comap of $E.I$ along $\mathrm{mapOnProdOver}\, c\, s$ — and the dual of the module of the ideal sheaf $(\ker p_\varepsilon)^r \cdot \bigl(\prod_m \ker (q\,m).1\bigr)^{r'}$.
--
--   This identifies the geometric fibre at $s$ of the line bundle attached to the relative divisor $r\varepsilon + r'W$ with the inverse of the corresponding product of ideals of $\Omega$-points of the fibre curve, converting divisor data on the relative curve into point-ideal data on the fibre. It is used in the construction of charts for the relative Picard functor, namely by [`AlgebraicGeometry.RelPicard.exists_split_injective_forall_subsingleton_H1_lineBundle_and_support_subset_of_twoSidedBlocks_of_bijective_sections`](thm.html#AlgebraicGeometry.RelPicard.exists_split_injective_forall_subsingleton_H1_lineBundle_and_support_subset_of_twoSidedBlocks_of_bijective_sections).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelEffCartierDiv_nonempty_lineBundle_pullbackAlong_iso_invModule_pow_ker_mul_pow_prod_ker.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra MonoidalCategory
  AlgebraicGeometry.SmoothProperCurve TensorProduct

theorem AlgebraicGeometry.RelEffCartierDiv.nonempty_lineBundle_pullbackAlong_iso_invModule_pow_ker_mul_pow_prod_ker
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {ρ : ℕ} (E : RelEffCartierDiv c ρ (𝟙 (Spec (CommRingCat.of R))))
    (r r' d : ℕ) {W : Scheme.{u}} (w : W ⟶ pullback c (𝟙 (Spec (CommRingCat.of R)))) [IsClosedImmersion w]
    [IsFinite (w ≫ pullback.snd c (𝟙 _))] [Flat (w ≫ pullback.snd c (𝟙 _))] [Etale (w ≫ pullback.snd c (𝟙 _))]
    (hEI : E.I = (sectionIdeal c ε (𝟙 _)) ^ r * w.ker ^ r')
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R))
    (q : Fin d → {p : Spec (CommRingCat.of Ω) ⟶ pullback c s // p ≫ pullback.snd c s = 𝟙 _})
    (hqinj : Function.Injective (fun m => (q m).1))
    (hqW : ∀ m, ∃ y : Spec (CommRingCat.of Ω) ⟶ W, (q m).1 ≫ mapOnProdOver c s (Category.comp_id s) = y ≫ w)
    (hqall : ∀ y : Spec (CommRingCat.of Ω) ⟶ W, y ≫ w ≫ pullback.snd c (𝟙 _) = s →
      ∃ m, (q m).1 ≫ mapOnProdOver c s (Category.comp_id s) = y ≫ w)
    (pε : {p : Spec (CommRingCat.of Ω) ⟶ pullback c s // p ≫ pullback.snd c s = 𝟙 _})
    (hpε : pε.1 ≫ pullback.fst c s = s ≫ ε.1) :
    Nonempty ((E.pullbackAlong s (Category.comp_id s)).lineBundle ≅
      ((pε.1.ker) ^ r * (∏ m, (q m).1.ker) ^ r').invModule) := by sorry
