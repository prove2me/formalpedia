-- Prove2me | Theorems.Thm_BrionAntiAffine_proposition_2_2
-- name    : BrionAntiAffine.proposition_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:34:53.177936+00:00
-- url     : https://prove2.me/theorems/4eb668d4-c95b-46f4-80bb-49c235ea79bd
-- title:
--   Proposition 2.2 — positive characteristic and finite fields
-- statement:
--   Let $G$ be an anti-affine algebraic group over a field $k$.
--
--   1. If $k$ has characteristic $p>0$, then $G$ is a semi-abelian variety.
--   2. If $k$ is finite, then $G$ is an abelian variety.
--
--   So the classification in positive characteristic only involves extensions by tori, and over finite fields there is nothing beyond abelian varieties.
--
--   **Formalization Note** The field is not assumed perfect in the first clause. A semi-abelian variety is an extension of an abelian variety by a torus, with all objects existential.
--
--   Differences from the source: none.
-- source:
--   M. Brion, Anti-affine algebraic groups, arXiv:0710.5211v3, Proposition 2.2, p.7

import Mathlib
import Definitions.Def_BrionAntiAffine_IsTorus

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

noncomputable section

namespace BrionAntiAffine

variable {k : Type u} [Field k]

/-- Proposition 2.2, Brion, arXiv:0710.5211v3, p.7. Any anti-affine algebraic group over a field of
characteristic `p > 0` (resp. over a finite field) is a semi-abelian variety (resp. an abelian
variety).

**Formalization Note.** `k` is not assumed perfect in the first clause. -/
theorem proposition_2_2 (G : Sch k) [GrpObj G] (hG : IsAlgebraicGroup G) (hanti : IsAntiAffine G) :
    (∀ p : ℕ, p.Prime → CharP k p → IsSemiAbelian G) ∧ (Finite k → IsAbelianVariety G) := by sorry

end BrionAntiAffine
