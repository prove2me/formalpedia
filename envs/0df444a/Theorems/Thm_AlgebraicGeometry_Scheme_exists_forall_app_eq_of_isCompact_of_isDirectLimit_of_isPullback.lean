-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_forall_app_eq_of_isCompact_of_isDirectLimit_of_isPullback
-- name    : AlgebraicGeometry.Scheme.exists_forall_app_eq_of_isCompact_of_isDirectLimit_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/548572f3-0206-5401-baf8-b2f1de298d09
-- title:
--   Finitely many sections over quasi-compact opens descend to one stage
-- statement:
--   Let $\iota$ be a nonempty directed preorder, $(G_i)_{i\in\iota}$ a family of commutative rings with transition ring homomorphisms $\varphi_{ij}:G_i\to G_j$ for $i\le j$ forming a directed system, and $R$ a commutative ring with ring homomorphisms $g_i:G_i\to R$ exhibiting $R$ as a direct limit of the system, i.e. every element of $R$ is $g_i(m)$ for some $i$ and $m\in G_i$, any two elements $m_i\in G_i$, $m_j\in G_j$ with $g_i(m_i)=g_j(m_j)$ become equal after transporting to some common $k\ge i,j$, and $g_j\circ\varphi_{ij}=g_i$. Fix $i\in\iota$ and a quasi-compact, quasi-separated morphism of schemes $f_X:X\to\operatorname{Spec}G_i$. Let $p:X_R\to X$ and $q:X_R\to\operatorname{Spec}R$ form a cartesian square with $f_X$ and $\operatorname{Spec}(g_i)$. Let $\kappa$ be finite, $W_k\subseteq X$ open with $W_k$ quasi-compact, and $a_k\in\Gamma(X_R,p^{-1}W_k)$ for each $k$. The assertion is that there exist $j\ge i$ and sections $b_k\in\Gamma(X\times_{\operatorname{Spec}G_i}\operatorname{Spec}G_j,\ \mathrm{pr}_1^{-1}W_k)$ such that for every morphism $c:X_R\to X\times_{\operatorname{Spec}G_i}\operatorname{Spec}G_j$ with $c$ followed by $\mathrm{pr}_1$ equal to $p$ and $c$ followed by $\mathrm{pr}_2$ equal to $q$ followed by $\operatorname{Spec}(g_j)$, each $k$, and every identification $e$ of $p^{-1}W_k$ with $c^{-1}(\mathrm{pr}_1^{-1}W_k)$, the pullback of $b_k$ along $c$, transported along $e$, equals $a_k$.
--
--   This is the finite-family form of the standard limit theorem for quasi-compact quasi-separated morphisms over a direct limit of affine bases (EGA IV₃ 8.5): finitely many sections over quasi-compact opens of the base-changed scheme all descend to a single stage $j$, the cartesian square being given abstractly rather than as the literal fibre product. It is obtained from the one-section version [`AlgebraicGeometry.Scheme.exists_app_eq_of_isCompact_of_isDirectLimit`](thm.html#AlgebraicGeometry.Scheme.exists_app_eq_of_isCompact_of_isDirectLimit) and is used in the descent of invertible modules, via [`AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_forall_app_unit_eq_of_isDirectLimit`](thm.html#AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_forall_app_unit_eq_of_isDirectLimit).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_exists_forall_app_eq_of_isCompact_of_isDirectLimit_of_isPullback.lean

import Mathlib
import Definitions.Def_Mathlib_Algebra_IsDirectLimit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

theorem AlgebraicGeometry.Scheme.exists_forall_app_eq_of_isCompact_of_isDirectLimit_of_isPullback
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    {G : ι → Type u} [∀ i, CommRing (G i)] (φ : ∀ i j : ι, i ≤ j → G i →+* G j)
    [DirectedSystem G fun i j h => ⇑(φ i j h)]
    {R : Type u} [CommRing R] (g : ∀ i, G i →+* R)
    (hR : IsDirectLimit (fun i j h => ⇑(φ i j h)) fun i => ⇑(g i))
    (i : ι) {X : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of (G i))) [QuasiCompact fX] [QuasiSeparated fX]
    {XR : Scheme.{u}} (p : XR ⟶ X) (q : XR ⟶ Spec (CommRingCat.of R))
    (hp : IsPullback p q fX (Spec.map (CommRingCat.ofHom (g i))))
    {κ : Type u} [Finite κ] (W : κ → X.Opens) (hW : ∀ k, IsCompact (W k : Set X))
    (a : ∀ k, Γ(XR, p ⁻¹ᵁ W k)) :
    ∃ (j : ι) (hij : i ≤ j)
      (b : ∀ k, Γ(Limits.pullback fX (Spec.map (CommRingCat.ofHom (φ i j hij))),
        (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij)))) ⁻¹ᵁ W k)),
      ∀ (c : XR ⟶ Limits.pullback fX (Spec.map (CommRingCat.ofHom (φ i j hij)))),
        c ≫ Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij))) = p →
        c ≫ Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (φ i j hij))) = q ≫ Spec.map (CommRingCat.ofHom (g j)) →
        ∀ (k : κ) (e : p ⁻¹ᵁ W k = c ⁻¹ᵁ ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij)))) ⁻¹ᵁ W k)),
          XR.presheaf.map (eqToHom e).op
            (c.app ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij)))) ⁻¹ᵁ W k) (b k)) = a k := by sorry
