-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_app_eq_app_of_isCompact_of_isDirectLimit
-- name    : AlgebraicGeometry.Scheme.exists_app_eq_app_of_isCompact_of_isDirectLimit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/1e5cf5f9-bbff-529c-a668-f2f8675d1e04
-- title:
--   Sections equal over the limit become equal at a finite stage
-- statement:
--   Let $\iota$ be a nonempty directed preorder, let $(G_k)_{k \in \iota}$ be commutative rings with ring homomorphisms $\varphi_{kl} : G_k \to G_l$ for $k \le l$ forming a directed system, and let $R$ be a commutative ring with ring homomorphisms $g_k : G_k \to R$ exhibiting $R$ as the direct limit, i.e. every element of $R$ is $g_k(x)$ for some $k$ and some $x \in G_k$; if $g_k(x) = g_l(y)$ then $\varphi_{km}(x) = \varphi_{lm}(y)$ for some $m \ge k, l$; and $g_l \circ \varphi_{kl} = g_k$. Fix $i \in \iota$, a scheme $X$ and a quasi-compact, quasi-separated morphism $f_X : X \to \operatorname{Spec} G_i$, an open $W \subseteq X$ whose underlying set is compact, and $j \ge i$. Let $t, t'$ be sections of the structure sheaf of the pullback $X \times_{\operatorname{Spec} G_i} \operatorname{Spec} G_j$ over the preimage of $W$ under the first projection. Assume that for every morphism $c : X \times_{\operatorname{Spec} G_i} \operatorname{Spec} R \to X \times_{\operatorname{Spec} G_i} \operatorname{Spec} G_j$ satisfying $\mathrm{pr}_1 \circ c = \mathrm{pr}_1$ and $\mathrm{pr}_2 \circ c = \operatorname{Spec}(g_j) \circ \mathrm{pr}_2$ one has $c^{*} t = c^{*} t'$ on the relevant open. Then there exists $j' \ge j$ such that every morphism $c : X \times_{\operatorname{Spec} G_i} \operatorname{Spec} G_{j'} \to X \times_{\operatorname{Spec} G_i} \operatorname{Spec} G_j$ with $\mathrm{pr}_1 \circ c = \mathrm{pr}_1$ and $\mathrm{pr}_2 \circ c = \operatorname{Spec}(\varphi_{jj'}) \circ \mathrm{pr}_2$ satisfies $c^{*} t = c^{*} t'$ over the preimage of $W$.
--
--   This is the injectivity half of the identification $\Gamma(\mathrm{pr}_R^{-1}W, \mathcal{O}) = \varinjlim_j \Gamma(\mathrm{pr}_{G_j}^{-1}W, \mathcal{O})$ for a quasi-compact open $W$ and a quasi-compact quasi-separated morphism to $\operatorname{Spec}$ of a filtered colimit of rings, in the style of EGA IV 8.5.2; the transition morphisms are quantified over, characterised by their compatibilities with the two projections, rather than constructed. It is used to descend equalities of sections to a finite stage, in particular for the cocycle and unit identities occurring in the limit arguments for modules and line bundles over such base changes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_exists_app_eq_app_of_isCompact_of_isDirectLimit.lean

import Mathlib
import Definitions.Def_Mathlib_Algebra_IsDirectLimit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

theorem AlgebraicGeometry.Scheme.exists_app_eq_app_of_isCompact_of_isDirectLimit
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    {G : ι → Type u} [∀ i, CommRing (G i)] (φ : ∀ i j : ι, i ≤ j → G i →+* G j)
    [DirectedSystem G fun i j h => ⇑(φ i j h)]
    {R : Type u} [CommRing R] (g : ∀ i, G i →+* R)
    (hR : IsDirectLimit (fun i j h => ⇑(φ i j h)) fun i => ⇑(g i))
    (i : ι) {X : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of (G i))) [QuasiCompact fX] [QuasiSeparated fX]
    (W : X.Opens) (hW : IsCompact (W : Set X)) (j : ι) (hij : i ≤ j)
    (t t' : Γ(Limits.pullback fX (Spec.map (CommRingCat.ofHom (φ i j hij))), (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij)))) ⁻¹ᵁ W))
    (h : ∀ (c : Limits.pullback fX (Spec.map (CommRingCat.ofHom (g i))) ⟶ Limits.pullback fX (Spec.map (CommRingCat.ofHom (φ i j hij)))),
        c ≫ Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij))) = Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (g i))) →
        c ≫ Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (φ i j hij))) = Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (g i))) ≫ Spec.map (CommRingCat.ofHom (g j)) →
        c.app ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij)))) ⁻¹ᵁ W) t = c.app ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij)))) ⁻¹ᵁ W) t') :
    ∃ (j' : ι) (hjj' : j ≤ j'),
      ∀ (c : Limits.pullback fX (Spec.map (CommRingCat.ofHom (φ i j' (hij.trans hjj')))) ⟶ Limits.pullback fX (Spec.map (CommRingCat.ofHom (φ i j hij)))),
        c ≫ Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij))) = Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j' (hij.trans hjj')))) →
        c ≫ Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (φ i j hij))) = Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (φ i j' (hij.trans hjj')))) ≫ Spec.map (CommRingCat.ofHom (φ j j' hjj')) →
        c.app ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij)))) ⁻¹ᵁ W) t = c.app ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij)))) ⁻¹ᵁ W) t' := by sorry
