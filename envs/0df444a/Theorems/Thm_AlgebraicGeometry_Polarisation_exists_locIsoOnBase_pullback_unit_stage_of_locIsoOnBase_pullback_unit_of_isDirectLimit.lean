-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_exists_locIsoOnBase_pullback_unit_stage_of_locIsoOnBase_pullback_unit_of_isDirectLimit
-- name    : AlgebraicGeometry.Polarisation.exists_locIsoOnBase_pullback_unit_stage_of_locIsoOnBase_pullback_unit_of_isDirectLimit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/5df75f06-26a2-5dab-b00f-ce7f3fc62d83
-- title:
--   Local triviality on the base descends to a finite stage
-- statement:
--   Let $\iota$ be a nonempty preordered type that is directed upwards, let $(G_i)_{i\in\iota}$ be commutative rings equipped with transition ring homomorphisms $\varphi_{ij}\colon G_i\to G_j$ for $i\le j$ forming a directed system, and let $R$ be a commutative ring with ring homomorphisms $g_i\colon G_i\to R$ exhibiting $R$ as the direct limit of the system in the sense of [`IsDirectLimit`](def/Mathlib_Algebra_IsDirectLimit.html#L8): every element of $R$ is $g_i(m)$ for some $i$ and some $m\in G_i$; whenever $g_i(m_i)=g_j(m_j)$ the two elements already agree after transport to some common $k\ge i,j$; and $g_j\circ\varphi_{ij}=g_i$. Fix $i\in\iota$, a scheme $X$ and a quasi-compact, quasi-separated morphism $f_X\colon X\to\operatorname{Spec}G_i$, together with a module $N$ on $X$ that is invertible, i.e. every point of $X$ has an open neighbourhood $U$ on which the restriction of $N$ is isomorphic to the unit module of $U$. Assume that the pull-back of $N$ along the first projection of $X\times_{\operatorname{Spec}G_i}\operatorname{Spec}R$ is locally trivial over the base in the following sense (`LocIsoOnBase` for the second projection): for every point $s$ of $\operatorname{Spec}R$ there is an open $U\ni s$ of $\operatorname{Spec}R$ such that, over the preimage of $U$ under the second projection, this pull-back is isomorphic to the unit module. Then there exist $k\in\iota$ and $i\le k$ such that the same local triviality over the base holds for $X\times_{\operatorname{Spec}G_i}\operatorname{Spec}G_k$, formed along $\operatorname{Spec}$ of $\varphi_{ik}$: the pull-back of $N$ along the first projection is, locally on $\operatorname{Spec}G_k$, isomorphic to the unit module.
--
--   This is a limit-of-schemes (noetherian approximation) statement: a property of an invertible module witnessed over the direct limit ring $R=\varinjlim G_i$ is already witnessed over some finite stage $G_k$. It is used in the construction of finitely generated, noetherian models for rigidified line bundles on relative Picard functors, where an identification over a limit ring must be pushed back to a model of finite type.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_exists_locIsoOnBase_pullback_unit_stage_of_locIsoOnBase_pullback_unit_of_isDirectLimit.lean

import Mathlib
import Definitions.Def_Mathlib_Algebra_IsDirectLimit
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Polarisation

universe u

theorem AlgebraicGeometry.Polarisation.exists_locIsoOnBase_pullback_unit_stage_of_locIsoOnBase_pullback_unit_of_isDirectLimit
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    {G : ι → Type u} [∀ i, CommRing (G i)] (φ : ∀ i j : ι, i ≤ j → G i →+* G j)
    [DirectedSystem G fun i j h => ⇑(φ i j h)]
    {R : Type u} [CommRing R] (g : ∀ i, G i →+* R)
    (hR : IsDirectLimit (fun i j h => ⇑(φ i j h)) fun i => ⇑(g i))
    (i : ι) {X : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of (G i))) [QuasiCompact fX] [QuasiSeparated fX]
    (N : X.Modules) (hN : Scheme.Modules.IsInvertible N)
    (h : LocIsoOnBase (Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (g i))))
      ((Scheme.Modules.pullback (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (g i))))).obj N)
      (𝟙_ ((Limits.pullback fX (Spec.map (CommRingCat.ofHom (g i)))).Modules))) :
    ∃ (k : ι) (hik : i ≤ k),
      LocIsoOnBase (Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (φ i k hik))))
        ((Scheme.Modules.pullback (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i k hik))))).obj N)
        (𝟙_ ((Limits.pullback fX (Spec.map (CommRingCat.ofHom (φ i k hik)))).Modules)) := by sorry
