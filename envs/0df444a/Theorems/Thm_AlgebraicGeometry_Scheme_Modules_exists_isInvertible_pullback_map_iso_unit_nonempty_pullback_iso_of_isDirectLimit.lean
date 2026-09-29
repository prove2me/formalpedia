-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_pullback_map_iso_unit_nonempty_pullback_iso_of_isDirectLimit
-- name    : AlgebraicGeometry.Scheme.Modules.exists_isInvertible_pullback_map_iso_unit_nonempty_pullback_iso_of_isDirectLimit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/62e8af82-eb0d-53fe-9e6a-ca83c5c22d15
-- title:
--   Descent of a trivialised invertible module through a direct limit
-- statement:
--   Let $\iota$ be a nonempty preorder that is directed upwards, let $(G_i)_{i\in\iota}$ be commutative rings equipped with transition ring homomorphisms $\varphi_{ij}\colon G_i\to G_j$ for $i\le j$ forming a directed system, and let $R$ be a commutative ring with ring homomorphisms $g_i\colon G_i\to R$ exhibiting $R$ as the direct limit of the system in the sense of [`IsDirectLimit`](def/Mathlib_Algebra_IsDirectLimit.html#L8): every element of $R$ is $g_i(x)$ for some $i$ and some $x\in G_i$, any two elements with the same image become equal after passing to a common larger index, and $g_j\circ\varphi_{ij}=g_i$. Fix $i\in\iota$, schemes $P$ and $X$ with quasi-compact, quasi-separated morphisms $f_P\colon P\to\operatorname{Spec}G_i$ and $f_X\colon X\to\operatorname{Spec}G_i$, and a morphism $s\colon X\to P$ over $\operatorname{Spec}G_i$, i.e. $s$ followed by $f_P$ equals $f_X$. Let $\mathcal L$ be a module on the fibre product $P\times_{\operatorname{Spec}G_i}\operatorname{Spec}R$ formed along $\operatorname{Spec}(g_i)$ which is invertible in the sense of `Scheme.Modules.IsInvertible`: every point has an open neighbourhood $U$ such that the restriction of $\mathcal L$ to $U$ is isomorphic to the unit sheaf of modules on $U$. Assume further that the pullback of $\mathcal L$ along the base change $X\times_{\operatorname{Spec}G_i}\operatorname{Spec}R\to P\times_{\operatorname{Spec}G_i}\operatorname{Spec}R$ of $s$ (the canonical map induced by $s$ and the identity of $\operatorname{Spec}R$) is isomorphic to the unit sheaf of modules. Then there exist an index $k\ge i$ and a module $\mathcal L_k$ on $P\times_{\operatorname{Spec}G_i}\operatorname{Spec}G_k$ (the fibre product along $\operatorname{Spec}(\varphi_{ik})$) such that: $\mathcal L_k$ is invertible in the same sense; the pullback of $\mathcal L_k$ along the base change of $s$ to $X\times_{\operatorname{Spec}G_i}\operatorname{Spec}G_k$ is isomorphic to the unit sheaf of modules; and for every morphism $c\colon P\times_{\operatorname{Spec}G_i}\operatorname{Spec}R\to P\times_{\operatorname{Spec}G_i}\operatorname{Spec}G_k$ whose composite with the first projection is the first projection, and whose composite with the second projection equals the second projection followed by $\operatorname{Spec}(g_k)$, the pullback of $\mathcal L_k$ along $c$ is isomorphic to $\mathcal L$. All isomorphism assertions are stated as nonemptiness of the relevant type of isomorphisms.
--
--   This is the module-theoretic half of the Noetherian-approximation (limit descent) package for rigidified line bundles: an invertible module over a limit base, together with a trivialisation along a section-like morphism, already exists with its trivialisation at a finite stage of the directed system, compatibly with any choice of comparison morphism. It is used in the construction of models of rigidified line bundles over finitely generated subalgebras, in the statements [`AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_fg_subalgebra_isPullback_prodStr_model`](thm.html#AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_fg_subalgebra_isPullback_prodStr_model) and [`AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_noetherian_descent_affineOpens_of_isPullback_of_isPullback`](thm.html#AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_noetherian_descent_affineOpens_of_isPullback_of_isPullback), and it combines the existence of an invertible model with the descent of isomorphisms between invertible modules through the limit.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_pullback_map_iso_unit_nonempty_pullback_iso_of_isDirectLimit.lean

import Mathlib
import Definitions.Def_Mathlib_Algebra_IsDirectLimit
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.exists_isInvertible_pullback_map_iso_unit_nonempty_pullback_iso_of_isDirectLimit
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    {G : ι → Type u} [∀ i, CommRing (G i)] (φ : ∀ i j : ι, i ≤ j → G i →+* G j)
    [DirectedSystem G fun i j h => ⇑(φ i j h)]
    {R : Type u} [CommRing R] (g : ∀ i, G i →+* R)
    (hR : IsDirectLimit (fun i j h => ⇑(φ i j h)) fun i => ⇑(g i))
    (i : ι) {P X : Scheme.{u}} (fP : P ⟶ Spec (CommRingCat.of (G i))) [QuasiCompact fP] [QuasiSeparated fP]
    (fX : X ⟶ Spec (CommRingCat.of (G i))) [QuasiCompact fX] [QuasiSeparated fX]
    (s : X ⟶ P) (hs : s ≫ fP = fX)
    (𝓛 : (Limits.pullback fP (Spec.map (CommRingCat.ofHom (g i)))).Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (htriv : Nonempty ((Scheme.Modules.pullback
        (Limits.pullback.map fX (Spec.map (CommRingCat.ofHom (g i))) fP (Spec.map (CommRingCat.ofHom (g i))) s (𝟙 _) (𝟙 _)
          (by rw [hs, Category.comp_id]) (by rw [Category.comp_id, Category.id_comp]))).obj 𝓛 ≅
      SheafOfModules.unit (Limits.pullback fX (Spec.map (CommRingCat.ofHom (g i)))).ringCatSheaf)) :
    ∃ (k : ι) (hik : i ≤ k) (𝓛k : (Limits.pullback fP (Spec.map (CommRingCat.ofHom (φ i k hik)))).Modules),
      Scheme.Modules.IsInvertible 𝓛k ∧
      Nonempty ((Scheme.Modules.pullback
          (Limits.pullback.map fX (Spec.map (CommRingCat.ofHom (φ i k hik))) fP (Spec.map (CommRingCat.ofHom (φ i k hik))) s (𝟙 _) (𝟙 _)
            (by rw [hs, Category.comp_id]) (by rw [Category.comp_id, Category.id_comp]))).obj 𝓛k ≅
        SheafOfModules.unit (Limits.pullback fX (Spec.map (CommRingCat.ofHom (φ i k hik)))).ringCatSheaf) ∧
      ∀ c : Limits.pullback fP (Spec.map (CommRingCat.ofHom (g i))) ⟶ Limits.pullback fP (Spec.map (CommRingCat.ofHom (φ i k hik))),
        c ≫ Limits.pullback.fst fP (Spec.map (CommRingCat.ofHom (φ i k hik))) = Limits.pullback.fst fP (Spec.map (CommRingCat.ofHom (g i))) →
        c ≫ Limits.pullback.snd fP (Spec.map (CommRingCat.ofHom (φ i k hik))) =
          Limits.pullback.snd fP (Spec.map (CommRingCat.ofHom (g i))) ≫ Spec.map (CommRingCat.ofHom (g k)) →
        Nonempty ((Scheme.Modules.pullback c).obj 𝓛k ≅ 𝓛) := by sorry
