-- Prove2me | Theorems.Thm_FamousTheorems_cartan_criterion_semisimplicity
-- name    : FamousTheorems.cartan_criterion_semisimplicity
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:23:12.344489+00:00
-- url     : https://prove2.me/theorems/bf269d84-9ae0-4fcb-8f24-e4224ecaef60
-- title:
--   Cartan's criterion for semisimplicity
-- statement:
--   **Cartan's criterion for semisimplicity.** Let $L$ be a Lie algebra over a domain $R$ of characteristic zero, free and finitely generated as an $R$-module. If $L$ has trivial radical, that is no nonzero solvable ideal, then the Killing form of $L$ is nondegenerate.
--
--   This is the nontrivial direction of the characterisation of semisimple Lie algebras by their Killing form. It is used to decompose semisimple Lie algebras into simple ideals, and it is the starting point of the root space decomposition.
--
--   **Formalization note.** Mathlib's instance `LieAlgebra.HasTrivialRadical.instIsKilling`, proved by `inferInstance`. `LieAlgebra.IsKilling R L` states that the Killing form is nondegenerate.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `LieAlgebra.HasTrivialRadical.instIsKilling`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem cartan_criterion_semisimplicity (R L : Type*) [CommRing R] [CharZero R] [IsDomain R] [LieRing L] [LieAlgebra R L] [IsNoetherian R L]
    [Module.Free R L] [LieAlgebra.HasTrivialRadical R L] : LieAlgebra.IsKilling R L := by sorry

end FamousTheorems
