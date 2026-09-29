-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_OrderedOpenFamily_exists_orderedAffineCover_inter_image_eq_inf
-- name    : AlgebraicGeometry.Scheme.OrderedOpenFamily.exists_orderedAffineCover_inter_image_eq_inf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/7e481f39-5889-5118-ab4b-ac19daace7b9
-- title:
--   Strip affine covers of intersections exist
-- statement:
--   Let $R$ be a commutative ring, $Z$ a scheme and $\pi : Z \to \operatorname{Spec} R$ a separated morphism. Let $\mathfrak A$ and $\mathfrak B$ be ordered open families on $Z$, each consisting of a finite linearly ordered index type together with a map from it to the opens of $Z$; write $\mathfrak A.U_i$ and $\mathfrak B.U_j$ for the corresponding opens. Assume that $\mathfrak A.U_i \sqcap \mathfrak B.U_j$ is an affine open for all indices $i, j$, and that $\bigsqcup_j \mathfrak B.U_j = \top$. Let $p$ be a natural number. Then for every $s$ in $\mathfrak A.\mathrm{Idx}\, p$, that is every strictly monotone map $s : \mathrm{Fin}(p+1) \to \mathfrak A.\iota$, there are an ordered affine cover $\mathfrak W_s$ of the open subscheme $\mathfrak A.\mathrm{inter}\, s = \bigsqcap_{k} \mathfrak A.U_{s(k)}$ — a finite linearly ordered index type with opens of that subscheme, each affine, whose supremum is $\top$ — and an order isomorphism $e_s : \mathfrak B.\iota \simeq \mathfrak W_s.\iota$, such that for every such $s$ and every $j \in \mathfrak B.\iota$ the image of the chart $\mathfrak W_s.U_{e_s(j)}$ under the open immersion $\mathfrak A.\mathrm{inter}\, s \to Z$ equals $\mathfrak A.\mathrm{inter}\, s \sqcap \mathfrak B.U_j$.
--
--   This supplies the affine charts needed to compute Čech cohomology on the intersections of one ordered open family using a second family as a tracing cover, with a single index type shared by all the intersections. It is used in the alternating-sum computation of the Euler characteristic of a Mumford bundle tensored with a pullback.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_OrderedOpenFamily_exists_orderedAffineCover_inter_image_eq_inf.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_BiCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.OrderedOpenFamily.exists_orderedAffineCover_inter_image_eq_inf
    {R : Type u} [CommRing R] {Z : Scheme.{u}} (π : Z ⟶ Spec (CommRingCat.of R)) [IsSeparated π]
    (𝔄 𝔅 : Z.OrderedOpenFamily) (haff : ∀ i j, IsAffineOpen (𝔄.U i ⊓ 𝔅.U j)) (hcov : ⨆ j, 𝔅.U j = ⊤) (p : ℕ) :
    ∃ (𝔚 : ∀ s : 𝔄.Idx p, ((𝔄.inter s : Z.Opens) : Scheme.{u}).OrderedAffineCover)
      (e : ∀ s : 𝔄.Idx p, 𝔅.ι ≃o (𝔚 s).ι),
      ∀ (s : 𝔄.Idx p) (j : 𝔅.ι), (𝔄.inter s).ι ''ᵁ (𝔚 s).U (e s j) = 𝔄.inter s ⊓ 𝔅.U j := by sorry
