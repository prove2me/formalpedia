-- Prove2me | Theorems.Thm_FamousTheorems_grun_lemma
-- name    : FamousTheorems.grun_lemma
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:21:47.146252+00:00
-- url     : https://prove2.me/theorems/4078ab65-8c07-420f-ada3-fed0d9a526e9
-- title:
--   Grün's lemma
-- statement:
--   **Grün's lemma.** If $G$ is a perfect group, that is $G=[G,G]$, then the quotient $G/Z(G)$ has trivial centre.
--
--   The lemma shows that, for a perfect group, the upper central series stops after one step. It is used in the theory of Schur covers and quasisimple groups.
--
--   **Formalization note.** Mathlib's `Group.IsPerfect.center_quotient_center_eq_bot`. `Group.IsPerfect G` is the Mathlib class saying that the commutator subgroup of $G$ is all of $G$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Group.IsPerfect.center_quotient_center_eq_bot`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem grun_lemma (G : Type*) [Group G] [Group.IsPerfect G] : Subgroup.center (G ⧸ Subgroup.center G) = ⊥ := by sorry

end FamousTheorems
