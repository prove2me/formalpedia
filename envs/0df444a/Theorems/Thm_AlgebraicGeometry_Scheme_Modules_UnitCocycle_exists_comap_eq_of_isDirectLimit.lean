-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_UnitCocycle_exists_comap_eq_of_isDirectLimit
-- name    : AlgebraicGeometry.Scheme.Modules.UnitCocycle.exists_comap_eq_of_isDirectLimit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/bc2d1b6a-5671-52ce-87aa-a5939643f47a
-- title:
--   Unit cocycles over a direct limit descend to a finite stage
-- statement:
--   Let $\iota$ be a nonempty directed preorder, let $(G_i)_{i\in\iota}$ be commutative rings with transition ring homomorphisms $\varphi_{ij}\colon G_i\to G_j$ for $i\le j$ forming a directed system, and let $R$ be a commutative ring with ring homomorphisms $g_i\colon G_i\to R$ exhibiting $R$ as the direct limit in the sense of [`IsDirectLimit`](def/Mathlib_Algebra_IsDirectLimit.html#L8) (every element of $R$ comes from some $G_i$; two elements with the same image agree after passing to a common later stage; the $g_i$ are compatible with the $\varphi_{ij}$). Fix $i$, a scheme $X$ and a quasi-compact, quasi-separated morphism $f_X\colon X\to\operatorname{Spec} G_i$. Let $\kappa$ be a finite type and $W\colon\kappa\to$ (opens of $X$) with each $W_k$ having compact underlying set. Write $\mathrm{pr}_T$ for the first projection of the pullback of $f_X$ along $\operatorname{Spec}$ of the relevant ring map. Assume $\bigsqcup_k \mathrm{pr}_R^{-1}W_k=\top$, and let $gc$ be a unit cocycle on the family $(\mathrm{pr}_R^{-1}W_k)_k$, i.e. sections $gc.u\,a\,b\in\Gamma(\mathrm{pr}_R^{-1}W_a\cap \mathrm{pr}_R^{-1}W_b)$ with $gc.u\,a\,a=1$ and $gc.u\,a\,b\cdot gc.u\,b\,c=gc.u\,a\,c$ after restriction to the triple intersection. Then there are $j\ge i$ and a unit cocycle $c$ on the family $(\mathrm{pr}_{G_j}^{-1}W_k)_k$ such that $\bigsqcup_k \mathrm{pr}_{G_j}^{-1}W_k=\top$ and such that for every morphism $c_X$ from the pullback over $R$ to the pullback over $G_j$ satisfying $c_X$ followed by $\mathrm{pr}_{G_j}$ equals $\mathrm{pr}_R$ and $c_X$ followed by the second projection equals the second projection followed by $\operatorname{Spec}$ of $g_j$, for all $a,b\in\kappa$ and every equality $e$ of opens identifying $\mathrm{pr}_R^{-1}W_a\cap\mathrm{pr}_R^{-1}W_b$ with $c_X^{-1}(\mathrm{pr}_{G_j}^{-1}W_a)\cap c_X^{-1}(\mathrm{pr}_{G_j}^{-1}W_b)$, the restriction along $e$ of the $(a,b)$ component of the pull-back $c.\mathrm{comap}\,c_X$ (whose components are the images of those of $c$ under $c_X$ on sections) equals $gc.u\,a\,b$.
--
--   This is a limit statement in the style of EGA IV, §8.5: Čech unit $1$-cocycles for a finite cover by preimages of quasi-compact opens on a base change to a direct limit of rings already exist, together with the covering property, at a finite stage of the system. It is used in the descent of invertible modules along such a limit, in [`AlgebraicGeometry.Scheme.Modules.exists_isInvertible_nonempty_pullback_iso_of_isInvertible_of_isDirectLimit`](thm.html#AlgebraicGeometry.Scheme.Modules.exists_isInvertible_nonempty_pullback_iso_of_isInvertible_of_isDirectLimit), and rests on the corresponding surjectivity and injectivity statements for sections over quasi-compact opens together with the spreading-out of the covering condition.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_UnitCocycle_exists_comap_eq_of_isDirectLimit.lean

import Mathlib
import Definitions.Def_Mathlib_Algebra_IsDirectLimit
import Definitions.Def_AlgebraicGeometry_ModulesGlueOfCocycle

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

theorem AlgebraicGeometry.Scheme.Modules.UnitCocycle.exists_comap_eq_of_isDirectLimit
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    {G : ι → Type u} [∀ i, CommRing (G i)] (φ : ∀ i j : ι, i ≤ j → G i →+* G j)
    [DirectedSystem G fun i j h => ⇑(φ i j h)]
    {R : Type u} [CommRing R] (g : ∀ i, G i →+* R)
    (hR : IsDirectLimit (fun i j h => ⇑(φ i j h)) fun i => ⇑(g i))
    (i : ι) {X : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of (G i))) [QuasiCompact fX] [QuasiSeparated fX]
    {κ : Type u} [Finite κ] (W : κ → X.Opens) (hW : ∀ k, IsCompact (W k : Set X))
    (hcov : (⨆ k, (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (g i)))) ⁻¹ᵁ W k) = ⊤)
    (gc : Scheme.Modules.UnitCocycle fun k => (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (g i)))) ⁻¹ᵁ W k) :
    ∃ (j : ι) (hij : i ≤ j) (c : Scheme.Modules.UnitCocycle fun k => (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij)))) ⁻¹ᵁ W k),
      (⨆ k, (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij)))) ⁻¹ᵁ W k) = ⊤ ∧
      ∀ (cX : Limits.pullback fX (Spec.map (CommRingCat.ofHom (g i))) ⟶ Limits.pullback fX (Spec.map (CommRingCat.ofHom (φ i j hij)))),
        cX ≫ Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij))) = Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (g i))) →
        cX ≫ Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (φ i j hij))) = Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (g i))) ≫ Spec.map (CommRingCat.ofHom (g j)) →
        ∀ (a b : κ)
          (e : (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (g i)))) ⁻¹ᵁ W a ⊓ (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (g i)))) ⁻¹ᵁ W b =
            cX ⁻¹ᵁ ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij)))) ⁻¹ᵁ W a) ⊓ cX ⁻¹ᵁ ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij)))) ⁻¹ᵁ W b)),
          (Limits.pullback fX (Spec.map (CommRingCat.ofHom (g i)))).presheaf.map (eqToHom e).op ((c.comap cX).u a b) = gc.u a b := by sorry
