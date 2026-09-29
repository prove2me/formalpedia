-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_nonempty_iso_pullback_of_nonempty_iso_pullback_of_isDirectLimit
-- name    : AlgebraicGeometry.Scheme.Modules.exists_nonempty_iso_pullback_of_nonempty_iso_pullback_of_isDirectLimit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/271bbaec-aedb-59d0-be7d-4acbd445e157
-- title:
--   Isomorphisms of invertible modules descend to a finite stage
-- statement:
--   Let $\iota$ be a nonempty preordered type, directed with respect to $\le$, let $(G_i)_{i\in\iota}$ be a family of commutative rings equipped with transition ring homomorphisms $\varphi_{ij}:G_i\to G_j$ for $i\le j$ forming a directed system of the underlying functions, and let $R$ be a commutative ring with ring homomorphisms $g_i:G_i\to R$ exhibiting $R$ as the direct limit in the sense of [`IsDirectLimit`](def/Mathlib_Algebra_IsDirectLimit.html#L8): every element of $R$ is $g_i(x)$ for some $i$ and some $x\in G_i$; whenever $g_i(x)=g_j(y)$ there is $k$ with $i\le k$, $j\le k$ and $\varphi_{ik}(x)=\varphi_{jk}(y)$; and $g_j\circ\varphi_{ij}=g_i$ for all $i\le j$. Fix an index $i$, a scheme $X$ and a morphism $f_X:X\to\operatorname{Spec} G_i$ that is quasi-compact and quasi-separated, and two sheaves of modules $\mathcal L_1,\mathcal L_2$ on $X$ which are invertible in the sense that every point of $X$ has an open neighbourhood $U$ such that the pullback of the module along the inclusion $U\hookrightarrow X$ admits an isomorphism to the unit sheaf of modules on $U$. Assume the pullbacks of $\mathcal L_1$ and $\mathcal L_2$ along the first projection of the fibre product of $f_X$ with $\operatorname{Spec}(g_i):\operatorname{Spec} R\to\operatorname{Spec} G_i$ are isomorphic (the type of isomorphisms is nonempty). Then there exist $j$ and a proof that $i\le j$ such that the pullbacks of $\mathcal L_1$ and $\mathcal L_2$ along the first projection of the fibre product of $f_X$ with $\operatorname{Spec}(\varphi_{ij})$ are already isomorphic.
--
--   This is the descent of an isomorphism of invertible modules from the base change to a direct limit of rings to a base change at a finite stage, in the style of the limit arguments of EGA IV 8.5 for finitely presented modules. It is used in the project to push isomorphisms of line bundles and of polarisations on abelian schemes down from a limit ring to a finitely generated subring, and is invoked by the corresponding statements for rigidified line bundles and for polarised abelian schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_nonempty_iso_pullback_of_nonempty_iso_pullback_of_isDirectLimit.lean

import Mathlib
import Definitions.Def_Mathlib_Algebra_IsDirectLimit
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.Scheme.Modules.exists_nonempty_iso_pullback_of_nonempty_iso_pullback_of_isDirectLimit
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    {G : ι → Type u} [∀ i, CommRing (G i)] (φ : ∀ i j : ι, i ≤ j → G i →+* G j)
    [DirectedSystem G fun i j h => ⇑(φ i j h)]
    {R : Type u} [CommRing R] (g : ∀ i, G i →+* R)
    (hR : IsDirectLimit (fun i j h => ⇑(φ i j h)) fun i => ⇑(g i))
    (i : ι) {X : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of (G i))) [QuasiCompact fX] [QuasiSeparated fX]
    (𝓛₁ 𝓛₂ : X.Modules) (h₁ : Scheme.Modules.IsInvertible 𝓛₁) (h₂ : Scheme.Modules.IsInvertible 𝓛₂)
    (hiso : Nonempty
      ((Scheme.Modules.pullback (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (g i))))).obj 𝓛₁ ≅
       (Scheme.Modules.pullback (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (g i))))).obj 𝓛₂)) :
    ∃ (j : ι) (hij : i ≤ j), Nonempty
      ((Scheme.Modules.pullback (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij))))).obj 𝓛₁ ≅
       (Scheme.Modules.pullback (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij))))).obj 𝓛₂) := by sorry
