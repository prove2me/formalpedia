-- Prove2me | Theorems.Thm_BrionAntiAffine_lemma_1_3
-- name    : BrionAntiAffine.lemma_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:33:29.390456+00:00
-- url     : https://prove2.me/theorems/f0136995-89df-4c42-b22c-05e42963eec1
-- title:
--   Lemma 1.3 — products, quotients, extensions
-- statement:
--   Let $G_1,G_2$ be connected group schemes of finite type over $k$.
--
--   1. $G_1\times G_2$ is anti-affine if and only if $G_1$ and $G_2$ are both anti-affine.
--   2. Given an exact sequence of group schemes
--   $$1\to G_1\to G\to G_2\to 1,$$
--   if $G$ is anti-affine, then so is $G_2$. Conversely, if $G_1$ and $G_2$ are both anti-affine, then so is $G$.
--
--   So the class of anti-affine groups is stable under products, quotients and extensions.
--
--   Differences from the source:
--   - encoding: an exact sequence of group schemes → IsExactSeq: homomorphisms, q faithfully flat and quasi-compact, i the kernel of q, all of finite type; reason: the convention of p.3 and the standard meaning
-- source:
--   M. Brion, Anti-affine algebraic groups, arXiv:0710.5211v3, Lemma 1.3, pp.4–5

import Mathlib
import Definitions.Def_BrionAntiAffine_IsExactSeq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

noncomputable section

namespace BrionAntiAffine

variable {k : Type u} [Field k]

/-- Lemma 1.3, Brion, arXiv:0710.5211v3, pp.4–5. Let `G₁, G₂` be connected group schemes. (i) `G₁ × G₂`
is anti-affine iff `G₁` and `G₂` are both anti-affine. (ii) Given an exact sequence
`1 → G₁ → G → G₂ → 1`, if `G` is anti-affine then so is `G₂`; conversely, if `G₁` and `G₂` are both
anti-affine, then so is `G`. -/
theorem lemma_1_3 :
    (∀ (G₁ G₂ : Sch k) [GrpObj G₁] [GrpObj G₂], IsFiniteTypeOver G₁ → IsFiniteTypeOver G₂ →
      ConnectedSpace G₁.left → ConnectedSpace G₂.left →
        (IsAntiAffine (G₁ ⊗ G₂) ↔ IsAntiAffine G₁ ∧ IsAntiAffine G₂)) ∧
    (∀ (G₁ G G₂ : Sch k) [GrpObj G₁] [GrpObj G] [GrpObj G₂] (i : G₁ ⟶ G) (q : G ⟶ G₂),
      ConnectedSpace G₁.left → ConnectedSpace G₂.left → IsExactSeq i q →
        (IsAntiAffine G → IsAntiAffine G₂) ∧
          (IsAntiAffine G₁ → IsAntiAffine G₂ → IsAntiAffine G)) := by sorry

end BrionAntiAffine
