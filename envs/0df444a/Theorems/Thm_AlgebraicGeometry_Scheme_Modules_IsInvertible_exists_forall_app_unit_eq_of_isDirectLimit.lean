-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_forall_app_unit_eq_of_isDirectLimit
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_forall_app_unit_eq_of_isDirectLimit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/96aadf48-7a8f-5546-9970-d018b4932d82
-- title:
--   Sections of an invertible module spread out over a direct limit
-- statement:
--   Let $\iota$ be a nonempty directed preorder, $(G_i)_{i\in\iota}$ a directed system of commutative rings with transition maps $\varphi_{ij}:G_i\to G_j$ for $i\le j$, and let $g_i:G_i\to R$ be ring maps into a commutative ring $R$ exhibiting $R$ as the direct limit in the sense of [`IsDirectLimit`](def/Mathlib_Algebra_IsDirectLimit.html#L8): every element of $R$ is $g_i(m)$ for some $i$ and some $m\in G_i$, any two elements with the same image in $R$ become equal at some later stage, and the $g_i$ are compatible with the $\varphi_{ij}$. Fix $i\in\iota$, a quasi-compact and quasi-separated morphism $f_X:X\to\operatorname{Spec} G_i$, and a square $p:X_R\to X$, $q:X_R\to\operatorname{Spec} R$ which is cartesian over $\operatorname{Spec}(g_i)$. Let $M$ be a module on $X$ which is invertible, in the sense that every point of $X$ has an open neighbourhood $U$ such that the pullback of $M$ along $U\hookrightarrow X$ is isomorphic to the unit module on $U$, and let $(s_k)_{k\in\kappa}$ be a finite family of global sections of $p^*M$. Then there exist $j\ge i$ and global sections $t_k$ of $\mathrm{pr}_1^*M$ on $X\times_{\operatorname{Spec} G_i}\operatorname{Spec} G_j$, where $\mathrm{pr}_1$ is the first projection of that pullback, such that for every morphism $c:X_R\to X\times_{\operatorname{Spec} G_i}\operatorname{Spec} G_j$ with $c$ followed by $\mathrm{pr}_1$ equal to $p$ and $c$ followed by the second projection equal to $q$ followed by $\operatorname{Spec}(g_j)$, there is an isomorphism $e:c^*\mathrm{pr}_1^*M\cong p^*M$ of modules on $X_R$ whose effect on global sections carries the image of $t_k$ under the unit of the pullback–pushforward adjunction for $c$ to $s_k$, for every $k$.
--
--   This is a spreading-out (limit) statement for sections of a line bundle: finitely many global sections of an invertible module pulled back to a limit base descend to a finite stage of the directed system, in the style of the limit theorems for quasi-compact quasi-separated morphisms. It is used in the construction of finitely generated subalgebras over which polarised abelian schemes and their projective presentations by sections are defined.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_forall_app_unit_eq_of_isDirectLimit.lean

import Mathlib
import Definitions.Def_Mathlib_Algebra_IsDirectLimit
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_forall_app_unit_eq_of_isDirectLimit
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    {G : ι → Type u} [∀ i, CommRing (G i)] (φ : ∀ i j : ι, i ≤ j → G i →+* G j)
    [DirectedSystem G fun i j h => ⇑(φ i j h)]
    {R : Type u} [CommRing R] (g : ∀ i, G i →+* R)
    (hR : IsDirectLimit (fun i j h => ⇑(φ i j h)) fun i => ⇑(g i))
    (i : ι) {X : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of (G i))) [QuasiCompact fX] [QuasiSeparated fX]
    {XR : Scheme.{u}} (p : XR ⟶ X) (q : XR ⟶ Spec (CommRingCat.of R))
    (hp : IsPullback p q fX (Spec.map (CommRingCat.ofHom (g i))))
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M)
    {κ : Type u} [Finite κ] (s : κ → Γ((Scheme.Modules.pullback p).obj M, ⊤)) :
    ∃ (j : ι) (hij : i ≤ j)
      (t : κ → Γ((Scheme.Modules.pullback
        (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij))))).obj M, ⊤)),
      ∀ (c : XR ⟶ Limits.pullback fX (Spec.map (CommRingCat.ofHom (φ i j hij)))),
        c ≫ Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij))) = p →
        c ≫ Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (φ i j hij))) = q ≫ Spec.map (CommRingCat.ofHom (g j)) →
        ∃ e : (Scheme.Modules.pullback c).obj ((Scheme.Modules.pullback
              (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij))))).obj M) ≅
            (Scheme.Modules.pullback p).obj M,
          ∀ k, e.hom.app ⊤ ((((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app _).app ⊤) (t k)) = s k := by sorry
