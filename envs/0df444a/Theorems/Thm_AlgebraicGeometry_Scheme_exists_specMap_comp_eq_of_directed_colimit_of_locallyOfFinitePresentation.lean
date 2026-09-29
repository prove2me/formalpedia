-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_specMap_comp_eq_of_directed_colimit_of_locallyOfFinitePresentation
-- name    : AlgebraicGeometry.Scheme.exists_specMap_comp_eq_of_directed_colimit_of_locallyOfFinitePresentation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/04b59c5c-6733-57c0-a0e6-27fe9be9f80d
-- title:
--   Finitely presented points over a directed colimit descend to a finite stage
-- statement:
--   Let $\iota$ be a nonempty directed preordered index type, let $S_i$ be commutative rings indexed by $i \in \iota$, and let $t_{ij} : S_i \to S_j$ be ring homomorphisms given for each $i \le j$, subject to $t_{ii} = \mathrm{id}$ and $t_{jk} \circ t_{ij} = t_{ik}$ for $i \le j \le k$. Let $L$ be a commutative ring equipped with ring homomorphisms $c_i : S_i \to L$ satisfying $c_j \circ t_{ij} = c_i$ for $i \le j$, such that every element of $L$ is of the form $c_i(y)$ for some $i$ and some $y \in S_i$, and such that whenever $c_i(y) = c_i(z)$ for $y, z \in S_i$ there is $j \ge i$ with $t_{ij}(y) = t_{ij}(z)$; thus the $c_i$ exhibit $L$ as the colimit of the system. Fix $i \in \iota$ and a morphism of schemes $\zeta : Z \to \operatorname{Spec} S_i$ which is affine and locally of finite presentation, together with a morphism $z : \operatorname{Spec} L \to Z$ whose composite with $\zeta$ is $\operatorname{Spec}(c_i)$. The conclusion is that there exist $j \ge i$ and a morphism $z_j : \operatorname{Spec} S_j \to Z$ with $z_j$ followed by $\zeta$ equal to $\operatorname{Spec}(t_{ij})$, and with $z$ equal to $\operatorname{Spec}(c_j)$ followed by $z_j$.
--
--   This is the existence (surjectivity) half of the standard statement that, for a morphism locally of finite presentation, points with values in a directed colimit of rings are already defined at a finite stage, here formulated with a hand-presented directed system rather than a categorical colimit. It is used in the construction of level structures on fake elliptic curves over Čerednik–Drinfeld data, where an $L$-valued point is spread out to a finite level $S_j$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_exists_specMap_comp_eq_of_directed_colimit_of_locallyOfFinitePresentation.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.exists_specMap_comp_eq_of_directed_colimit_of_locallyOfFinitePresentation
    (ι : Type u) [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    (S : ι → Type u) [∀ i, CommRing (S i)]
    (t : ∀ i j, i ≤ j → (S i →+* S j))
    (ht₁ : ∀ i (h : i ≤ i), t i i h = RingHom.id (S i))
    (ht₂ : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k), (t j k hjk).comp (t i j hij) = t i k (hij.trans hjk))
    (L : Type u) [CommRing L] (c : ∀ i, S i →+* L)
    (hc : ∀ i j (h : i ≤ j), (c j).comp (t i j h) = c i)
    (hcsurj : ∀ x : L, ∃ (i : ι) (y : S i), c i y = x)
    (hcker : ∀ (i : ι) (y z : S i), c i y = c i z → ∃ (j : ι) (h : i ≤ j), t i j h y = t i j h z)
    (i : ι) {Z : Scheme.{u}} (ζ : Z ⟶ Spec (CommRingCat.of (S i))) [IsAffineHom ζ] [LocallyOfFinitePresentation ζ]
    (z : Spec (CommRingCat.of L) ⟶ Z) (hz : z ≫ ζ = Spec.map (CommRingCat.ofHom (c i))) :
    ∃ (j : ι) (hij : i ≤ j) (zj : Spec (CommRingCat.of (S j)) ⟶ Z),
      zj ≫ ζ = Spec.map (CommRingCat.ofHom (t i j hij)) ∧ z = Spec.map (CommRingCat.ofHom (c j)) ≫ zj := by sorry
