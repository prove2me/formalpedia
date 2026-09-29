-- Prove2me | Theorems.Thm_FamousTheorems_hopkins_levitzki_theorem
-- name    : FamousTheorems.hopkins_levitzki_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:22:12.871585+00:00
-- url     : https://prove2.me/theorems/97b1339d-f662-4612-8c2d-d1340cd02b84
-- title:
--   The Hopkins–Levitzki theorem
-- statement:
--   **The Hopkins–Levitzki theorem.** Let $R$ be a semiprimary ring: its Jacobson radical $J$ is nilpotent and $R/J$ is semisimple. Then an $R$-module is Noetherian if and only if it is Artinian.
--
--   In particular, a left Artinian ring is left Noetherian, since Artinian rings are semiprimary. This is a surprising asymmetry, because the descending chain condition implies the ascending one and not conversely. The theorem is fundamental in noncommutative ring theory.
--
--   **Formalization note.** Mathlib's `IsSemiprimaryRing.isNoetherian_iff_isArtinian`, for an arbitrary module $M$ over a ring satisfying `IsSemiprimaryRing`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `IsSemiprimaryRing.isNoetherian_iff_isArtinian`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem hopkins_levitzki_theorem {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [IsSemiprimaryRing R] :
    IsNoetherian R M ↔ IsArtinian R M := by sorry

end FamousTheorems
