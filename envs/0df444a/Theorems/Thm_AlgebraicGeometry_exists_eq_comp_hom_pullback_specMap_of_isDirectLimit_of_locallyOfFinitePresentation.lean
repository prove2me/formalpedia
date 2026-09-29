-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_eq_comp_hom_pullback_specMap_of_isDirectLimit_of_locallyOfFinitePresentation
-- name    : AlgebraicGeometry.exists_eq_comp_hom_pullback_specMap_of_isDirectLimit_of_locallyOfFinitePresentation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/57b4751c-a8e9-5cf2-8faa-105e6cf5a01d
-- title:
--   Factoring a morphism over a direct limit through a finite stage
-- statement:
--   Let $\iota$ be a non-empty directed preorder, let $(G_i)_{i\in\iota}$ be commutative rings equipped with ring homomorphisms $\varphi_{ij}\colon G_i\to G_j$ for $i\le j$ forming a directed system, and let $R$ be a commutative ring with ring homomorphisms $g_i\colon G_i\to R$ exhibiting $R$ as the direct limit in the sense of the predicate [`IsDirectLimit`](def/Mathlib_Algebra_IsDirectLimit.html#L8): every element of $R$ is $g_i(m)$ for some $i$ and some $m\in G_i$; if $g_i(m_i)=g_j(m_j)$ then $\varphi_{ik}(m_i)=\varphi_{jk}(m_j)$ for some $k\ge i,j$; and $g_j\circ\varphi_{ij}=g_i$ for all $i\le j$. Fix an index $i$, schemes $W,V$, a morphism $w\colon W\to\operatorname{Spec}G_i$ that is quasi-compact and quasi-separated, and a morphism $v\colon V\to\operatorname{Spec}G_i$ that is locally of finite presentation. Let $a$ be a morphism from the pullback of $w$ along $\operatorname{Spec}(g_i)$ to $V$ with $a$ followed by $v$ equal to the first projection of that pullback followed by $w$. Then there are an index $j\ge i$ and a morphism $a_j$ from the pullback of $w$ along $\operatorname{Spec}(\varphi_{ij})$ to $V$ such that $a_j$ followed by $v$ equals the first projection followed by $w$, and such that for every morphism $\kappa$ from the pullback along $\operatorname{Spec}(g_i)$ to the pullback along $\operatorname{Spec}(\varphi_{ij})$ satisfying $\kappa$ followed by the first projection equals the first projection, and $\kappa$ followed by the second projection equals the second projection followed by $\operatorname{Spec}(g_j)$, one has $a=\kappa$ followed by $a_j$. All types and schemes live in a single universe.
--
--   This is the existence (surjectivity) half of the limit formula for morphisms into a scheme locally of finite presentation, EGA IV 8.8.2: $\varinjlim_j \operatorname{Hom}_{G_i}(W\times_{G_i}G_j,V)\to \operatorname{Hom}_{G_i}(W\times_{G_i}R,V)$ is surjective. The canonical comparison morphism $W\times_{G_i}R\to W\times_{G_i}G_j$ is not named but characterised by its two projections, the factorisation being asserted for every morphism $\kappa$ with those properties. It is used in the descent of such a morphism to a finitely generated subalgebra.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_eq_comp_hom_pullback_specMap_of_isDirectLimit_of_locallyOfFinitePresentation.lean

import Mathlib
import Definitions.Def_Mathlib_Algebra_IsDirectLimit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_eq_comp_hom_pullback_specMap_of_isDirectLimit_of_locallyOfFinitePresentation
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    {G : ι → Type u} [∀ i, CommRing (G i)] (φ : ∀ i j : ι, i ≤ j → G i →+* G j)
    [DirectedSystem G fun i j h => ⇑(φ i j h)]
    {R : Type u} [CommRing R] (g : ∀ i, G i →+* R)
    (hR : IsDirectLimit (fun i j h => ⇑(φ i j h)) fun i => ⇑(g i))
    (i : ι) {W V : Scheme.{u}} (w : W ⟶ Spec (CommRingCat.of (G i))) (v : V ⟶ Spec (CommRingCat.of (G i)))
    [QuasiCompact w] [QuasiSeparated w] [LocallyOfFinitePresentation v]
    (a : pullback w (Spec.map (CommRingCat.ofHom (g i))) ⟶ V)
    (ha : a ≫ v = pullback.fst w (Spec.map (CommRingCat.ofHom (g i))) ≫ w) :
    ∃ (j : ι) (hij : i ≤ j) (aⱼ : pullback w (Spec.map (CommRingCat.ofHom (φ i j hij))) ⟶ V),
      aⱼ ≫ v = pullback.fst w (Spec.map (CommRingCat.ofHom (φ i j hij))) ≫ w ∧
      ∀ κ : pullback w (Spec.map (CommRingCat.ofHom (g i))) ⟶ pullback w (Spec.map (CommRingCat.ofHom (φ i j hij))),
        κ ≫ pullback.fst w (Spec.map (CommRingCat.ofHom (φ i j hij))) =
          pullback.fst w (Spec.map (CommRingCat.ofHom (g i))) →
        κ ≫ pullback.snd w (Spec.map (CommRingCat.ofHom (φ i j hij))) =
          pullback.snd w (Spec.map (CommRingCat.ofHom (g i))) ≫ Spec.map (CommRingCat.ofHom (g j)) →
        a = κ ≫ aⱼ := by sorry
