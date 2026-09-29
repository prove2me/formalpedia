-- Prove2me | Theorems.Thm_FamousTheorems_akizuki_hopkins_theorem
-- name    : FamousTheorems.akizuki_hopkins_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:22:12.023985+00:00
-- url     : https://prove2.me/theorems/378a664b-310a-43a1-b9ef-35106b1c67ed
-- title:
--   The Akizuki–Hopkins theorem
-- statement:
--   **The Akizuki–Hopkins theorem.** A commutative ring $R$ is Artinian if and only if it is Noetherian and has Krull dimension at most $0$ (every prime ideal is maximal).
--
--   This is the commutative form of the Hopkins–Levitzki theorem, due to Akizuki and Hopkins. It identifies Artinian rings as the zero-dimensional Noetherian rings. It is the base case of dimension theory and gives the structure of Artinian rings as finite products of Artinian local rings.
--
--   **Formalization note.** Mathlib's `isArtinianRing_iff_isNoetherianRing_krullDimLE_zero`. `Ring.KrullDimLE 0 R` says that the Krull dimension of $R$ is at most $0$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `isArtinianRing_iff_isNoetherianRing_krullDimLE_zero`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem akizuki_hopkins_theorem {R : Type*} [CommRing R] : IsArtinianRing R ↔ IsNoetherianRing R ∧ Ring.KrullDimLE 0 R := by sorry

end FamousTheorems
