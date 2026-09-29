-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_forall_app_eq_app_of_isCompact_of_isDirectLimit_of_isPullback
-- name    : AlgebraicGeometry.Scheme.exists_forall_app_eq_app_of_isCompact_of_isDirectLimit_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/de7c82f0-ac7f-5546-afe3-5608ac104e34
-- title:
--   Finitely many section pairs agreeing over the limit agree at one stage
-- statement:
--   Let $\iota$ be a nonempty directed preorder, let $(G_i)_{i\in\iota}$ be commutative rings equipped with ring homomorphisms $\varphi_{ij} : G_i \to G_j$ for $i \le j$ forming a directed system, and let $R$ be a commutative ring with homomorphisms $g_i : G_i \to R$ exhibiting $R$ as the direct limit in the sense that every element of $R$ is $g_i(m)$ for some $i$ and $m \in G_i$, that $g_i(m_i) = g_j(m_j)$ implies $\varphi_{ik}(m_i) = \varphi_{jk}(m_j)$ for some $k \ge i, j$, and that $g_j \circ \varphi_{ij} = g_i$. Fix $i \in \iota$ and a quasi-compact, quasi-separated morphism $f_X : X \to \operatorname{Spec} G_i$ of schemes, and let $p : X_R \to X$, $q : X_R \to \operatorname{Spec} R$ be morphisms making the square with $f_X$ and $\operatorname{Spec}(g_i)$ cartesian. Fix $j \ge i$, write $X_j$ for the chosen pullback of $f_X$ along $\operatorname{Spec}(\varphi_{ij})$ with projections $\mathrm{pr}_1, \mathrm{pr}_2$, let $\kappa$ be a finite type and $W_k \subseteq X$ ($k \in \kappa$) open subsets whose underlying sets are compact, and let $t_k, t'_k \in \Gamma(X_j, \mathrm{pr}_1^{-1}W_k)$. Assume that for every morphism $c : X_R \to X_j$ with $c \,;\, \mathrm{pr}_1 = p$ and $c \,;\, \mathrm{pr}_2 = q \,;\, \operatorname{Spec}(g_j)$ one has $c^{\sharp}(t_k) = c^{\sharp}(t'_k)$ on $\mathrm{pr}_1^{-1}W_k$ for all $k$. Then there exist $j' \ge j$ such that for every morphism $c' : X_{j'} \to X_j$ with $c' \,;\, \mathrm{pr}_1 = \mathrm{pr}_1$ and $c' \,;\, \mathrm{pr}_2 = \mathrm{pr}_2 \,;\, \operatorname{Spec}(\varphi_{jj'})$ one has $c'^{\sharp}(t_k) = c'^{\sharp}(t'_k)$ on $\mathrm{pr}_1^{-1}W_k$ for all $k \in \kappa$, where $X_{j'}$ denotes the pullback of $f_X$ along $\operatorname{Spec}(\varphi_{ij'})$.
--
--   This is the finite-family form, with the base change to the limit presented as an arbitrary cartesian square rather than the chosen pullback, of the standard descent of identities of sections along a limit of affine base schemes (as in EGA IV₃, §8). It is used in the construction of invertible modules over schemes at a finite stage of a direct system, via [`AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_forall_app_unit_eq_of_isDirectLimit`](thm.html#AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_forall_app_unit_eq_of_isDirectLimit).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_exists_forall_app_eq_app_of_isCompact_of_isDirectLimit_of_isPullback.lean

import Mathlib
import Definitions.Def_Mathlib_Algebra_IsDirectLimit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

theorem AlgebraicGeometry.Scheme.exists_forall_app_eq_app_of_isCompact_of_isDirectLimit_of_isPullback
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    {G : ι → Type u} [∀ i, CommRing (G i)] (φ : ∀ i j : ι, i ≤ j → G i →+* G j)
    [DirectedSystem G fun i j h => ⇑(φ i j h)]
    {R : Type u} [CommRing R] (g : ∀ i, G i →+* R)
    (hR : IsDirectLimit (fun i j h => ⇑(φ i j h)) fun i => ⇑(g i))
    (i : ι) {X : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of (G i))) [QuasiCompact fX] [QuasiSeparated fX]
    {XR : Scheme.{u}} (p : XR ⟶ X) (q : XR ⟶ Spec (CommRingCat.of R))
    (hp : IsPullback p q fX (Spec.map (CommRingCat.ofHom (g i))))
    (j : ι) (hij : i ≤ j)
    {κ : Type u} [Finite κ] (W : κ → X.Opens) (hW : ∀ k, IsCompact (W k : Set X))
    (t t' : ∀ k, Γ(Limits.pullback fX (Spec.map (CommRingCat.ofHom (φ i j hij))),
      (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij)))) ⁻¹ᵁ W k))
    (h : ∀ (c : XR ⟶ Limits.pullback fX (Spec.map (CommRingCat.ofHom (φ i j hij)))),
      c ≫ Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij))) = p →
      c ≫ Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (φ i j hij))) = q ≫ Spec.map (CommRingCat.ofHom (g j)) →
      ∀ k, c.app ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij)))) ⁻¹ᵁ W k) (t k) =
        c.app ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij)))) ⁻¹ᵁ W k) (t' k)) :
    ∃ (j' : ι) (hjj' : j ≤ j'),
      ∀ (c' : Limits.pullback fX (Spec.map (CommRingCat.ofHom (φ i j' (hij.trans hjj')))) ⟶
          Limits.pullback fX (Spec.map (CommRingCat.ofHom (φ i j hij)))),
        c' ≫ Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij))) =
          Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j' (hij.trans hjj')))) →
        c' ≫ Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (φ i j hij))) =
          Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (φ i j' (hij.trans hjj')))) ≫ Spec.map (CommRingCat.ofHom (φ j j' hjj')) →
        ∀ k, c'.app ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij)))) ⁻¹ᵁ W k) (t k) =
          c'.app ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij)))) ⁻¹ᵁ W k) (t' k) := by sorry
