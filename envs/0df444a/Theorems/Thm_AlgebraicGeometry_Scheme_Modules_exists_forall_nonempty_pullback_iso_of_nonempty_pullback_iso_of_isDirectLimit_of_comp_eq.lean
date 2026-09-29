-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_forall_nonempty_pullback_iso_of_nonempty_pullback_iso_of_isDirectLimit_of_comp_eq
-- name    : AlgebraicGeometry.Scheme.Modules.exists_forall_nonempty_pullback_iso_of_nonempty_pullback_iso_of_isDirectLimit_of_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/9d026039-56b9-5b13-a53c-72938f067505
-- title:
--   Descent of an isomorphism of invertible modules to a finite stage
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} S$ a quasi-compact, quasi-separated morphism. Let $\iota$ be a nonempty directed preorder, $(G_i)_{i\in\iota}$ a family of commutative rings with ring maps $\varphi_{ij} : G_i \to G_j$ for $i \le j$ forming a directed system, $K$ a commutative ring and $g_i : G_i \to K$ maps exhibiting $K$ as the direct limit in the sense of [`IsDirectLimit`](def/Mathlib_Algebra_IsDirectLimit.html#L8): every element of $K$ is $g_i(x)$ for some $i$ and $x \in G_i$; if $g_i(x_i) = g_j(x_j)$ then $x_i$ and $x_j$ have a common image at some $k \ge i,j$; and $g_j \circ \varphi_{ij} = g_i$. Let $s_i : S \to G_i$ and $s_K : S \to K$ satisfy $\varphi_{ij} \circ s_i = s_j$ and $g_i \circ s_i = s_K$ for all $i \le j$. Fix $i_0$ and two modules $\mathcal L_1, \mathcal L_2$ on the scheme $A \times_{\operatorname{Spec} S} \operatorname{Spec} G_{i_0}$ (the pullback of $f$ along $\operatorname{Spec}(s_{i_0})$), each invertible in the sense that every point has an open neighbourhood $U$ on which the restriction along $U \hookrightarrow X$ is isomorphic to the unit sheaf of modules. Let $\rho : A \times_{\operatorname{Spec} S} \operatorname{Spec} K \to A \times_{\operatorname{Spec} S} \operatorname{Spec} G_{i_0}$ be a morphism commuting with the first projections to $A$ and with second projection equal to the second projection followed by $\operatorname{Spec}(g_{i_0})$, and suppose $\rho^*\mathcal L_1 \cong \rho^*\mathcal L_2$. Then there exist $j \ge i_0$ such that for every morphism $\rho' : A \times_{\operatorname{Spec} S} \operatorname{Spec} G_j \to A \times_{\operatorname{Spec} S} \operatorname{Spec} G_{i_0}$ compatible with the projections to $A$ and with $\operatorname{Spec}(\varphi_{i_0 j})$ on the base, one has $\rho'^*\mathcal L_1 \cong \rho'^*\mathcal L_2$.
--
--   This is the limit-descent statement for isomorphisms of invertible modules (a scheme-theoretic form of the statement that $\operatorname{Hom}$ between finitely presented quasi-coherent modules commutes with the relevant directed limit of qcqs bases), packaged in the form where the base change from stage $i_0$ to the limit, and from $i_0$ to a later stage $j$, is given by a single pullback square rather than an iterated one. It is used in the construction of polarisations, where an isomorphism of line bundles known over a limit field or ring must be realised over a finite stage.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_forall_nonempty_pullback_iso_of_nonempty_pullback_iso_of_isDirectLimit_of_comp_eq.lean

import Mathlib
import Definitions.Def_Mathlib_Algebra_IsDirectLimit
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Modules.exists_forall_nonempty_pullback_iso_of_nonempty_pullback_iso_of_isDirectLimit_of_comp_eq
    {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) [QuasiCompact f] [QuasiSeparated f]
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    {G : ι → Type u} [∀ i, CommRing (G i)] (φ : ∀ i j : ι, i ≤ j → G i →+* G j)
    [DirectedSystem G fun i j h => ⇑(φ i j h)]
    {K : Type u} [CommRing K] (g : ∀ i, G i →+* K)
    (hK : IsDirectLimit (fun i j h => ⇑(φ i j h)) fun i => ⇑(g i))
    (s : ∀ i, S →+* G i) (hs : ∀ (i j : ι) (h : i ≤ j), (φ i j h).comp (s i) = s j)
    (sK : S →+* K) (hsK : ∀ i, (g i).comp (s i) = sK)
    (i₀ : ι) (𝓛₁ 𝓛₂ : (Limits.pullback f (Spec.map (CommRingCat.ofHom (s i₀)))).Modules)
    (h₁ : Scheme.Modules.IsInvertible 𝓛₁) (h₂ : Scheme.Modules.IsInvertible 𝓛₂)
    (ρ : Limits.pullback f (Spec.map (CommRingCat.ofHom sK)) ⟶ Limits.pullback f (Spec.map (CommRingCat.ofHom (s i₀))))
    (hρ₁ : ρ ≫ Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (s i₀))) = Limits.pullback.fst f (Spec.map (CommRingCat.ofHom sK)))
    (hρ₂ : ρ ≫ Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (s i₀))) =
      Limits.pullback.snd f (Spec.map (CommRingCat.ofHom sK)) ≫ Spec.map (CommRingCat.ofHom (g i₀)))
    (hiso : Nonempty ((Scheme.Modules.pullback ρ).obj 𝓛₁ ≅ (Scheme.Modules.pullback ρ).obj 𝓛₂)) :
    ∃ (j : ι) (hij : i₀ ≤ j),
      ∀ ρ' : Limits.pullback f (Spec.map (CommRingCat.ofHom (s j))) ⟶ Limits.pullback f (Spec.map (CommRingCat.ofHom (s i₀))),
        ρ' ≫ Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (s i₀))) = Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (s j))) →
        ρ' ≫ Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (s i₀))) =
          Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (s j))) ≫ Spec.map (CommRingCat.ofHom (φ i₀ j hij)) →
        Nonempty ((Scheme.Modules.pullback ρ').obj 𝓛₁ ≅ (Scheme.Modules.pullback ρ').obj 𝓛₂) := by sorry
