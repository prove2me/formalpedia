-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isAffineOpen_isFrameOn_preimage_of_isDirectLimit
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isAffineOpen_isFrameOn_preimage_of_isDirectLimit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/9e82210c-f242-5ee8-93d7-a7ac1feca670
-- title:
--   Invertible module framed over affine opens from a finite stage
-- statement:
--   Let $\iota$ be a nonempty directed preorder, let $(G_i)_{i\in\iota}$ be commutative rings equipped with transition ring homomorphisms $\varphi_{ij} : G_i \to G_j$ for $i \le j$ forming a directed system, and let $R$ be a commutative ring with ring homomorphisms $g_i : G_i \to R$ exhibiting $R$ as the direct limit of the system (every element of $R$ comes from some $G_i$; two elements with the same image agree after passing to a common later stage; the $g_i$ are compatible with the $\varphi_{ij}$). Fix $i \in \iota$, a scheme $X$ and a quasi-compact, quasi-separated morphism $f_X : X \to \operatorname{Spec} G_i$, and let $\mathcal{L}$ be a module over the structure sheaf of the pullback $X_R := X \times_{\operatorname{Spec} G_i} \operatorname{Spec} R$ (the fibre product of $f_X$ and $\operatorname{Spec}$ of $g_i$) which is invertible in the sense that every point of $X_R$ has an open neighbourhood $U$ such that the pullback of $\mathcal{L}$ along the inclusion of $U$ is isomorphic to the unit module over the structure sheaf of $U$. Then there are $j \ge i$, a natural number $n$, and a family $W_k$, indexed by $k$ in a copy of $\operatorname{Fin} n$, of open subsets of $X_{G_j} := X \times_{\operatorname{Spec} G_i} \operatorname{Spec} G_j$ (the pullback of $f_X$ along $\operatorname{Spec}$ of $\varphi_{ij}$), each of which is an affine open, with the following property: for every morphism $c : X_R \to X_{G_j}$ whose composite with the first projection of $X_{G_j}$ is the first projection of $X_R$ and whose composite with the second projection of $X_{G_j}$ equals the second projection of $X_R$ followed by $\operatorname{Spec}$ of $g_j$, the preimages $c^{-1}W_k$ cover $X_R$ (their supremum is $\top$), and there are sections $s_k \in \Gamma(\mathcal{L}, c^{-1}W_k)$ such that each $s_k$ is a frame on $c^{-1}W_k$, i.e. for every open $W \le c^{-1}W_k$ the map $a \mapsto a \cdot (s_k|_W)$ from $\Gamma(\mathcal{O}_{X_R}, W)$ to $\Gamma(\mathcal{L}, W)$ is bijective.
--
--   This is the limit-theoretic step, in the style of EGA IV §8, which spreads a trivialisation of an invertible module on the base change of a quasi-compact quasi-separated $X$ to the direct limit $R$ out to a finite trivialising affine cover defined already at a finite stage $G_j$. It is the input to [`AlgebraicGeometry.Scheme.Modules.exists_isInvertible_nonempty_pullback_iso_of_isInvertible_of_isDirectLimit`](thm.html#AlgebraicGeometry.Scheme.Modules.exists_isInvertible_nonempty_pullback_iso_of_isInvertible_of_isDirectLimit), in the development of invertible modules and the relative Picard functor; the local existence of frames for an invertible module is supplied by [`AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isFrameOn`](thm.html#AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isFrameOn).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isAffineOpen_isFrameOn_preimage_of_isDirectLimit.lean

import Mathlib
import Definitions.Def_Mathlib_Algebra_IsDirectLimit
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isAffineOpen_isFrameOn_preimage_of_isDirectLimit
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    {G : ι → Type u} [∀ i, CommRing (G i)] (φ : ∀ i j : ι, i ≤ j → G i →+* G j)
    [DirectedSystem G fun i j h => ⇑(φ i j h)]
    {R : Type u} [CommRing R] (g : ∀ i, G i →+* R)
    (hR : IsDirectLimit (fun i j h => ⇑(φ i j h)) fun i => ⇑(g i))
    (i : ι) {X : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of (G i))) [QuasiCompact fX] [QuasiSeparated fX]
    (𝓛 : (Limits.pullback fX (Spec.map (CommRingCat.ofHom (g i)))).Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) :
    ∃ (j : ι) (hij : i ≤ j) (n : ℕ) (W : ULift.{u} (Fin n) → (Limits.pullback fX (Spec.map (CommRingCat.ofHom (φ i j hij)))).Opens),
      (∀ k, IsAffineOpen (W k)) ∧
      ∀ (c : Limits.pullback fX (Spec.map (CommRingCat.ofHom (g i))) ⟶ Limits.pullback fX (Spec.map (CommRingCat.ofHom (φ i j hij)))),
        c ≫ Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij))) = Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (g i))) →
        c ≫ Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (φ i j hij))) = Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (g i))) ≫ Spec.map (CommRingCat.ofHom (g j)) →
        (⨆ k, c ⁻¹ᵁ W k) = ⊤ ∧
        ∃ s : ∀ k, Γ(𝓛, c ⁻¹ᵁ W k), ∀ k, Scheme.Modules.IsFrameOn (s k) (c ⁻¹ᵁ W k) := by sorry
