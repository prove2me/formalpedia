-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_forall_specMap_base_mem_of_isDirectLimit
-- name    : AlgebraicGeometry.exists_forall_specMap_base_mem_of_isDirectLimit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/ea5611f5-23e0-57a2-ae60-ec1688a11094
-- title:
--   Open conditions on Spec descend to a finite stage
-- statement:
--   Let $\iota$ be a nonempty preorder that is directed upwards, let $G : \iota \to \mathrm{Type}$ be a family of commutative rings, and for each $i \le j$ let $\varphi_{ij} : G_i \to G_j$ be a ring homomorphism, the underlying maps forming a directed system (so $\varphi_{ii}$ is the identity and $\varphi_{jk}\circ\varphi_{ij} = \varphi_{ik}$). Let $R$ be a commutative ring and $g_i : G_i \to R$ ring homomorphisms whose underlying maps exhibit $R$ as the direct limit of the system in the sense of [`IsDirectLimit`](def/Mathlib_Algebra_IsDirectLimit.html#L8): every element of $R$ is of the form $g_i(m)$ for some $i$ and some $m \in G_i$; whenever $g_i(m_i) = g_j(m_j)$ there is $k$ with $i \le k$, $j \le k$ and $\varphi_{ik}(m_i) = \varphi_{jk}(m_j)$; and $g_j \circ \varphi_{ij} = g_i$ for all $i \le j$. Fix $i \in \iota$ and an open subscheme-theoretic open $W$ of $\operatorname{Spec} G_i$, and assume that for every point $p$ of $\operatorname{Spec} R$ the image of $p$ under the underlying continuous map of $\operatorname{Spec}(g_i)$ lies in $W$. Then there exist $j$ and a proof of $i \le j$ such that every point $q$ of $\operatorname{Spec} G_j$ is carried into $W$ by the underlying map of $\operatorname{Spec}(\varphi_{ij})$.
--
--   This is the standard permanence statement for limits of affine schemes: an open condition satisfied on the limit $\operatorname{Spec}$ of a directed system of rings is already satisfied at some finite stage (cf. EGA IV 8.10.5), with no finiteness or noetherian hypotheses. It is used in the proof that local finite presentation can be tested on directed colimits, and in a descent-to-a-stage argument for local isomorphisms on bases of pullbacks.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_forall_specMap_base_mem_of_isDirectLimit.lean

import Mathlib
import Definitions.Def_Mathlib_Algebra_IsDirectLimit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_forall_specMap_base_mem_of_isDirectLimit
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    {G : ι → Type u} [∀ i, CommRing (G i)] (φ : ∀ i j : ι, i ≤ j → G i →+* G j)
    [DirectedSystem G fun i j h => ⇑(φ i j h)]
    {R : Type u} [CommRing R] (g : ∀ i, G i →+* R)
    (hR : IsDirectLimit (fun i j h => ⇑(φ i j h)) fun i => ⇑(g i))
    (i : ι) (W : (Spec (CommRingCat.of (G i))).Opens)
    (hW : ∀ p : Spec (CommRingCat.of R), (Spec.map (CommRingCat.ofHom (g i))).base p ∈ W) :
    ∃ (j : ι) (hij : i ≤ j), ∀ q : Spec (CommRingCat.of (G j)), (Spec.map (CommRingCat.ofHom (φ i j hij))).base q ∈ W := by sorry
