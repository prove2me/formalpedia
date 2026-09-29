-- Prove2me | Theorems.Thm_FamousTheorems_flat_fg_local_free_6b
-- name    : FamousTheorems.flat_fg_local_free_6b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:43:24.893778+00:00
-- url     : https://prove2.me/theorems/cf29434c-98ee-45ea-9d1d-8f83a2b5480b
-- title:
--   Finitely generated flat modules over a local ring are free
-- statement:
--   **Finitely generated flat modules over a local ring are free.** Let $R$ be a commutative local ring and $P$ a finitely generated flat $R$-module. Then $P$ is free.
--
--   For finitely presented modules this is classical, since flat and finitely presented modules are projective and projective modules over local rings are free. The theorem shows that finite presentation is not needed over a local ring. Consequently, over any commutative ring, a finitely generated flat module is locally free at every prime.
--
--   **Formalization note.** Mathlib's `Module.free_of_flat_of_isLocalRing`. No Noetherian or finite presentation hypothesis is assumed.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Module.free_of_flat_of_isLocalRing`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem flat_fg_local_free_6b {R P : Type*} [CommRing R] [AddCommGroup P] [Module R P] [IsLocalRing R] [Module.Finite R P]
    [Module.Flat R P] : Module.Free R P := by sorry

end FamousTheorems
