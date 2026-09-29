-- Prove2me | Theorems.Thm_FamousTheorems_finite_unit_subgroup_domain_cyclic
-- name    : FamousTheorems.finite_unit_subgroup_domain_cyclic
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:38:18.722763+00:00
-- url     : https://prove2.me/theorems/86a2f258-cc7b-4ce4-be35-659a89653daa
-- title:
--   Finite subgroups of the multiplicative group of a domain are cyclic
-- statement:
--   **Finite subgroups of the multiplicative group of a domain are cyclic.** Let $R$ be an integral domain. Every finite subgroup of the unit group $R^\times$ is cyclic.
--
--   In particular, the multiplicative group of a finite field is cyclic (existence of primitive roots modulo $p$), and the $n$-th roots of unity in any field form a cyclic group. The proof uses the fact that a polynomial of degree $d$ has at most $d$ roots in a domain.
--
--   **Formalization note.** Mathlib's `isCyclic_subgroup_units`, for a subgroup `S` of `Rˣ` in a commutative ring `R` that is a domain.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `isCyclic_subgroup_units`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem finite_unit_subgroup_domain_cyclic {R : Type*} [CommRing R] [IsDomain R] (S : Subgroup Rˣ) [Finite S] : IsCyclic S := by sorry

end FamousTheorems
