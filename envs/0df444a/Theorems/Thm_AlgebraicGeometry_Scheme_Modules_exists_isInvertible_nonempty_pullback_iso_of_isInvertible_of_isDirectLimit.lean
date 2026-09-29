-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_nonempty_pullback_iso_of_isInvertible_of_isDirectLimit
-- name    : AlgebraicGeometry.Scheme.Modules.exists_isInvertible_nonempty_pullback_iso_of_isInvertible_of_isDirectLimit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/2e84fdab-b8b2-568a-a12c-6de535f47aaf
-- title:
--   Invertible modules on a limit descend to a finite stage
-- statement:
--   Let $\iota$ be a nonempty directed preorder, let $(G_i)_{i\in\iota}$ be commutative rings with transition homomorphisms $\varphi_{ij}\colon G_i \to G_j$ for $i \le j$ forming a directed system, and let $R$ be a commutative ring with homomorphisms $g_i \colon G_i \to R$ exhibiting $R$ as the direct limit in the sense of [`IsDirectLimit`](def/Mathlib_Algebra_IsDirectLimit.html#L8): every element of $R$ is $g_i(m)$ for some $i$ and some $m \in G_i$, two elements $m_i \in G_i$, $m_j \in G_j$ with the same image agree after transition to some common $k \ge i, j$, and $g_j \circ \varphi_{ij} = g_i$. Fix $i \in \iota$ and a quasi-compact, quasi-separated morphism of schemes $f_X \colon X \to \operatorname{Spec} G_i$, and let $\mathcal L$ be a module on the pullback $X \times_{\operatorname{Spec} G_i} \operatorname{Spec} R$ (along $\operatorname{Spec}$ of $g_i$) which is invertible, i.e. every point has an open neighbourhood $U$ such that the restriction of $\mathcal L$ to $U$ is isomorphic to the unit module on $U$. Then there exist $j \ge i$ and an invertible module $\mathcal L_j$ on $X \times_{\operatorname{Spec} G_i} \operatorname{Spec} G_j$ (along $\operatorname{Spec}$ of $\varphi_{ij}$) such that for every morphism $c_X$ between these two pullbacks satisfying $c_X$ followed by the first projection equals the first projection, and $c_X$ followed by the second projection equals the second projection followed by $\operatorname{Spec}$ of $g_j$, the pullback of $\mathcal L_j$ along $c_X$ is isomorphic to $\mathcal L$.
--
--   This is the surjectivity half of the statement that $\operatorname{Pic}(X_R) = \operatorname{colim}_{j \ge i} \operatorname{Pic}(X_{G_j})$ for a quasi-compact quasi-separated $X$ over $\operatorname{Spec} G_i$: line bundles on the limit already exist at a finite stage. It is used in the descent of polarised abelian schemes to finitely generated subalgebras and in the corresponding statement over algebraic field extensions, where line bundles must be pushed back to a Noetherian or finitely generated base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_nonempty_pullback_iso_of_isInvertible_of_isDirectLimit.lean

import Mathlib
import Definitions.Def_Mathlib_Algebra_IsDirectLimit
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.Scheme.Modules.exists_isInvertible_nonempty_pullback_iso_of_isInvertible_of_isDirectLimit
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    {G : ι → Type u} [∀ i, CommRing (G i)] (φ : ∀ i j : ι, i ≤ j → G i →+* G j)
    [DirectedSystem G fun i j h => ⇑(φ i j h)]
    {R : Type u} [CommRing R] (g : ∀ i, G i →+* R)
    (hR : IsDirectLimit (fun i j h => ⇑(φ i j h)) fun i => ⇑(g i))
    (i : ι) {X : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of (G i))) [QuasiCompact fX] [QuasiSeparated fX]
    (𝓛 : (Limits.pullback fX (Spec.map (CommRingCat.ofHom (g i)))).Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) :
    ∃ (j : ι) (hij : i ≤ j) (𝓛j : (Limits.pullback fX (Spec.map (CommRingCat.ofHom (φ i j hij)))).Modules),
      Scheme.Modules.IsInvertible 𝓛j ∧
      ∀ cX : Limits.pullback fX (Spec.map (CommRingCat.ofHom (g i))) ⟶
          Limits.pullback fX (Spec.map (CommRingCat.ofHom (φ i j hij))),
        cX ≫ Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij))) =
          Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (g i))) →
        cX ≫ Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (φ i j hij))) =
          Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (g i))) ≫ Spec.map (CommRingCat.ofHom (g j)) →
        Nonempty ((Scheme.Modules.pullback cX).obj 𝓛j ≅ 𝓛) := by sorry
