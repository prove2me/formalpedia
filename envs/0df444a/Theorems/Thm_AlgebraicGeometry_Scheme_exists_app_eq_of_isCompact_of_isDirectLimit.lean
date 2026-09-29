-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_app_eq_of_isCompact_of_isDirectLimit
-- name    : AlgebraicGeometry.Scheme.exists_app_eq_of_isCompact_of_isDirectLimit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/3185c0dd-0847-593e-90c3-53487f15667b
-- title:
--   Sections over a quasi-compact open descend to a finite stage
-- statement:
--   Let $\iota$ be a nonempty directed preorder, let $(G_i)_{i\in\iota}$ be commutative rings equipped with ring homomorphisms $\varphi_{ij}\colon G_i\to G_j$ for $i\le j$ forming a directed system, let $R$ be a commutative ring and let $g_i\colon G_i\to R$ be ring homomorphisms exhibiting $R$ as the direct limit in the sense of [`IsDirectLimit`](def/Mathlib_Algebra_IsDirectLimit.html#L8): every element of $R$ is $g_i(m)$ for some $i$ and some $m\in G_i$; whenever $g_i(m_i)=g_j(m_j)$ there is $k\ge i,j$ with $\varphi_{ik}(m_i)=\varphi_{jk}(m_j)$; and $g_j\circ\varphi_{ij}=g_i$. Fix $i\in\iota$ and a quasi-compact, quasi-separated morphism of schemes $f_X\colon X\to\operatorname{Spec} G_i$, an open $W\subseteq X$ whose underlying set is compact, and a section $s$ of the structure sheaf of the pullback $X_R:=X\times_{\operatorname{Spec} G_i}\operatorname{Spec} R$ over the preimage of $W$ under the first projection. Then there are $j\ge i$ and a section $t$ over the preimage of $W$ in $X_{G_j}:=X\times_{\operatorname{Spec} G_i}\operatorname{Spec} G_j$ such that for every morphism $c\colon X_R\to X_{G_j}$ commuting with the first projections to $X$ and satisfying that $c$ followed by the second projection equals the second projection of $X_R$ followed by $\operatorname{Spec}(g_j)$, and for every proof $e$ that the preimage of $W$ in $X_R$ equals the $c$-preimage of the preimage of $W$ in $X_{G_j}$, the image of $t$ under $c$ on sections, transported along $e$, equals $s$.
--
--   This is the surjectivity half of the statement that for a quasi-compact quasi-separated $X$ over $\operatorname{Spec} G_i$ and a quasi-compact open $W\subseteq X$ the sections of the structure sheaf over the preimage of $W$ in the base change to the direct limit $R$ are the direct limit of the corresponding groups over the stages $G_j$; the matching uniqueness statement is [`AlgebraicGeometry.Scheme.exists_app_eq_app_of_isCompact_of_isDirectLimit`](thm.html#AlgebraicGeometry.Scheme.exists_app_eq_app_of_isCompact_of_isDirectLimit). It is used in the limit arguments [`AlgebraicGeometry.Scheme.exists_forall_app_eq_of_isCompact_of_isDirectLimit_of_isPullback`](thm.html#AlgebraicGeometry.Scheme.exists_forall_app_eq_of_isCompact_of_isDirectLimit_of_isPullback) and [`AlgebraicGeometry.Scheme.Modules.UnitCocycle.exists_comap_eq_of_isDirectLimit`](thm.html#AlgebraicGeometry.Scheme.Modules.UnitCocycle.exists_comap_eq_of_isDirectLimit).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_exists_app_eq_of_isCompact_of_isDirectLimit.lean

import Mathlib
import Definitions.Def_Mathlib_Algebra_IsDirectLimit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

theorem AlgebraicGeometry.Scheme.exists_app_eq_of_isCompact_of_isDirectLimit
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    {G : ι → Type u} [∀ i, CommRing (G i)] (φ : ∀ i j : ι, i ≤ j → G i →+* G j)
    [DirectedSystem G fun i j h => ⇑(φ i j h)]
    {R : Type u} [CommRing R] (g : ∀ i, G i →+* R)
    (hR : IsDirectLimit (fun i j h => ⇑(φ i j h)) fun i => ⇑(g i))
    (i : ι) {X : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of (G i))) [QuasiCompact fX] [QuasiSeparated fX]
    (W : X.Opens) (hW : IsCompact (W : Set X))
    (s : Γ(Limits.pullback fX (Spec.map (CommRingCat.ofHom (g i))), (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (g i)))) ⁻¹ᵁ W)) :
    ∃ (j : ι) (hij : i ≤ j) (t : Γ(Limits.pullback fX (Spec.map (CommRingCat.ofHom (φ i j hij))), (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij)))) ⁻¹ᵁ W)),
      ∀ (c : Limits.pullback fX (Spec.map (CommRingCat.ofHom (g i))) ⟶ Limits.pullback fX (Spec.map (CommRingCat.ofHom (φ i j hij)))),
        c ≫ Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij))) = Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (g i))) →
        c ≫ Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (φ i j hij))) = Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (g i))) ≫ Spec.map (CommRingCat.ofHom (g j)) →
        ∀ e : (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (g i)))) ⁻¹ᵁ W = c ⁻¹ᵁ ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij)))) ⁻¹ᵁ W),
          (Limits.pullback fX (Spec.map (CommRingCat.ofHom (g i)))).presheaf.map (eqToHom e).op (c.app ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij)))) ⁻¹ᵁ W) t) = s := by sorry
