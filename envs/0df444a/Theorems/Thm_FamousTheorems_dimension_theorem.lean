-- Prove2me | Theorems.Thm_FamousTheorems_dimension_theorem
-- name    : FamousTheorems.dimension_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:14:59.397316+00:00
-- url     : https://prove2.me/theorems/25ec698e-8e46-4e9b-b902-822aa9cb3440
-- title:
--   The dimension theorem for vector spaces (invariant basis number)
-- statement:
--   **The dimension theorem for vector spaces.** Any two bases of a module over a ring with the invariant basis number property have the same cardinality. In particular this holds for vector spaces over a field, and more generally over any nonzero commutative ring.
--
--   This makes the dimension of a vector space (or the rank of a free module) well defined. It is the foundation for dimension counting throughout linear algebra, including the rank–nullity theorem and the classification of finite-dimensional spaces up to isomorphism.
--
--   **Formalization note.** Mathlib's `mk_eq_mk_of_basis`. Index types may live in different universes, so cardinalities are compared after `Cardinal.lift`. `InvariantBasisNumber R` is satisfied by all division rings and nontrivial commutative rings.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `mk_eq_mk_of_basis`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

universe u v w w'

theorem dimension_theorem {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M] [InvariantBasisNumber R]
    {ι : Type w} {ι' : Type w'} (b : Module.Basis ι R M) (b' : Module.Basis ι' R M) :
    Cardinal.lift.{w'} (Cardinal.mk ι) = Cardinal.lift.{w} (Cardinal.mk ι') := by sorry

end FamousTheorems
