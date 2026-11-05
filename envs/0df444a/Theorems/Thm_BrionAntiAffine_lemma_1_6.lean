-- Prove2me | Theorems.Thm_BrionAntiAffine_lemma_1_6
-- name    : BrionAntiAffine.lemma_1_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:32:42.085321+00:00
-- url     : https://prove2.me/theorems/f239157f-bfc8-4ef1-8a39-81a58418f46f
-- title:
--   Lemma 1.6 — multiplication by $n$ is an isogeny
-- statement:
--   Let $G$ be an anti-affine algebraic group over $k$ and $n$ a non-zero integer. Then the multiplication map
--
--   $$n_G:G\to G,\qquad x\mapsto nx$$
--
--   is an isogeny. This divisibility is the main ingredient of the classification in positive characteristic.
--
--   **Formalization Note** $n_G$ is the $n$-th power of the identity in the group $\mathrm{Hom}(G,G)$, defined for any group object, so commutativity is not assumed. An isogeny is a finite surjective homomorphism.
--
--   Differences from the source:
--   - encoding: an isogeny → a homomorphism whose underlying morphism is finite and surjective; reason: a surjective homomorphism of group schemes of finite type has finite kernel exactly when it is finite
-- source:
--   M. Brion, Anti-affine algebraic groups, arXiv:0710.5211v3, Lemma 1.6, p.6

import Mathlib
import Definitions.Def_BrionAntiAffine_AntiAffineOver

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

noncomputable section

namespace BrionAntiAffine

variable {k : Type u} [Field k]

/-- Lemma 1.6, Brion, arXiv:0710.5211v3, p.6. Let `G` be an anti-affine algebraic group and `n` a
non-zero integer. Then the multiplication map `n_G : G → G`, `x ↦ nx`, is an isogeny.

**Formalization Note.** `n_G` is the `n`-th power of `𝟙 G` in the group `G ⟶ G`, defined in any group
object, so commutativity is not assumed. An isogeny is a finite surjective homomorphism. -/
theorem lemma_1_6 (G : Sch k) [GrpObj G] (hG : IsAlgebraicGroup G) (hanti : IsAntiAffine G)
    (n : ℤ) (hn : n ≠ 0) :
    IsMonHom ((𝟙 G) ^ n) ∧ IsFinite ((𝟙 G) ^ n : G ⟶ G).left ∧
      Surjective ((𝟙 G) ^ n : G ⟶ G).left := by sorry

end BrionAntiAffine
