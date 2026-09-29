-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_forall_subsingleton_H1_sectionsOf_fibreModule_chartModule_of_smooth
-- name    : AlgebraicGeometry.RelPicard.exists_forall_subsingleton_H1_sectionsOf_fibreModule_chartModule_of_smooth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/249c8239-5021-568b-82a8-f5b48e69bc00
-- title:
--   A chart divisor killing check H¹ on a smooth geometric fibre
-- statement:
--   Let $R$ be a noetherian commutative ring, $c\colon C\to\operatorname{Spec}R$ proper and flat, $U\subseteq C$ an open subscheme with $U\hookrightarrow C$ followed by $c$ smooth of relative dimension $1$, and $\varepsilon$ a morphism $\operatorname{Spec}R\to C$ with $\varepsilon\circ$ nothing, i.e. satisfying $\varepsilon \cdot c=\mathrm{id}$, whose image lies in $U$. Assume: for every $R$-algebra $A$ the structure map $A\to\Gamma(C\times_{\operatorname{Spec}R}\operatorname{Spec}A,\top)$ is bijective; naturals $g,e,r$ with $g+e=r$ and $2g\le r+1$; and for every algebraically closed field $k$, every $x\colon\operatorname{Spec}k\to\operatorname{Spec}R$ and every two-affine open cover of the corresponding fibre, the $k$-dimension of the $H^1$ of the two-chart Čech complex of the structure module equals $g$. Further data: rings $B_i$ ($i<M$) that are $R$-algebras, morphisms $z_i\colon\operatorname{Spec}B_i\to C$ over $\operatorname{Spec}R$ with images in $U$ and pairwise disjoint, degrees $1\le\deg i\le b$ with $r\,b^{e}+e<M$, for each $i$ an injective family $\sigma_{i,\bullet}$ of $\deg i$ sections of $c$ each factoring through $z_i$, and for every algebraically closed $R$-field $\Omega$ a bijection between $R$-algebra maps $B_i\to\Omega$ and $\operatorname{Fin}(\deg i)$; an index type $\iota$, an indexing $\mathrm{idx}$ of injective $a\colon\operatorname{Fin}e\to\operatorname{Fin}M$ together with a choice $m$ of labels, and relative effective Cartier divisors $D_\gamma(\cdot)$ of degree $e$ over the identity base whose ideal at $\mathrm{idx}(a,m)$ is the product over $j$ of the kernel ideals of the graphs of the $\sigma_{a(j),m(a(j))}$. Finally, let $t\colon T\to\operatorname{Spec}R$, let $L$ be a rigidified line bundle on $C\times_{\operatorname{Spec}R}T$ (an invertible module trivialised along the rigidifying section) which is fibrewise algebraically equivalent to zero, and let $s\colon\operatorname{Spec}k\to T$ with $k$ algebraically closed be such that the fibre $C\times_{\operatorname{Spec}R}\operatorname{Spec}k$ along $s\cdot t$ is smooth, geometrically irreducible, and has image contained in $U$. Then there is an index $i\in\iota$ such that for every two-affine open cover of the fibre $(C\times_{\operatorname{Spec}R}T)\times_T\operatorname{Spec}k$, the first two-chart Čech cohomology of the restriction to that fibre of $L\otimes((\mathcal I_\varepsilon)^{r})^{\vee}\otimes\mathcal I_{D_\gamma(i),T}$ is a subsingleton, where $\mathcal I_\varepsilon$ is the kernel ideal of the rigidifying section, $(\cdot)^\vee$ the dual module, and $\mathcal I_{D_\gamma(i),T}$ the ideal module of the pullback of $D_\gamma(i)$ along $t$.
--
--   This is the general-position statement underlying the construction of charts for the relative Picard functor: among the divisors built from $e$-element blocks of disjoint $R$-rational blocks in $U$, one can be chosen so that the twist of a fibrewise algebraically trivial rigidified line bundle by $r\varepsilon$ and minus that divisor has vanishing first Čech cohomology on a prescribed smooth, geometrically irreducible geometric fibre. It feeds the covering hypothesis of [`AlgebraicGeometry.RelPicard.exists_chart_subsingleton_H1_fibre_of_blocks_of_injective`](thm.html#AlgebraicGeometry.RelPicard.exists_chart_subsingleton_H1_fibre_of_blocks_of_injective).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_forall_subsingleton_H1_sectionsOf_fibreModule_chartModule_of_smooth.lean

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
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra

theorem AlgebraicGeometry.RelPicard.exists_forall_subsingleton_H1_sectionsOf_fibreModule_chartModule_of_smooth
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c] [Flat c]
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (hεU : Set.range ε.1 ⊆ (U : Set C))
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))
    (g e r : ℕ) (hr : g + e = r) (hgr : 2 * g ≤ r + 1)
    (hg : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover),
      Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
        (SheafOfModules.unit (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).ringCatSheaf)).H1 = g)

    {M : ℕ} (B : Fin M → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)] (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ C)
    (hz : ∀ i, z i ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R (B i))))
    (hzU : ∀ i, Set.range (z i).base ⊆ (U : Set C)) (hzdisj : Pairwise fun i j => Disjoint (Set.range (z i).base) (Set.range (z j).base))
    (deg : Fin M → ℕ) (hdeg : ∀ i, 1 ≤ deg i) {b : ℕ} (hdegb : ∀ i, deg i ≤ b) (hMlt : r * b ^ e + e < M)
    (σ : ∀ i, Fin (deg i) → SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (hσinj : ∀ i, Function.Injective (σ i))
    (hσ : ∀ i m, ∃ y : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of (B i)), (σ i m).1 = y ≫ z i)
    (eB : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra R Ω] (i : Fin M), (B i →ₐ[R] Ω) ≃ Fin (deg i))
    {ι : Type u} (idx : {a : Fin e → Fin M // Function.Injective a} → (∀ i, Fin (deg i)) → ι)
    (Dγ : ι → RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R))))
    (hDγ : ∀ a m, (Dγ (idx a m)).I = prodKerGraph c (fun j => (σ (a.1 j) (m (a.1 j))).1) (fun j => (σ (a.1 j) (m (a.1 j))).2))

    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (L : RigidifiedLineBundle c ε t) (hL : FibrewiseAlgEquivZero L)
    (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T) (hsm : Smooth (pullback.snd c (s ≫ t)))
    (hgoodirr : GeometricallyIrreducible (pullback.snd c (s ≫ t))) (hgoodU : Set.range (pullback.fst c (s ≫ t)).base ⊆ (U : Set C)) :
    ∃ i : ι, ∀ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
        (L.L ⊗ (sectionTwist c ε t r ⊗ ((Dγ i).pullbackAlong t (Category.comp_id t)).idealModule)))).H1 := by sorry
