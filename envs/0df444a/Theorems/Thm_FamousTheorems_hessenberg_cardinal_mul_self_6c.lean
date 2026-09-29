-- Prove2me | Theorems.Thm_FamousTheorems_hessenberg_cardinal_mul_self_6c
-- name    : FamousTheorems.hessenberg_cardinal_mul_self_6c
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:46:47.892504+00:00
-- url     : https://prove2.me/theorems/ac941d5f-bd51-4a59-b473-3a30ab335a0a
-- title:
--   Hessenberg's theorem: κ·κ = κ for infinite cardinals
-- statement:
--   **Hessenberg's theorem.** For every infinite cardinal $\kappa$,
--   $$\kappa\cdot\kappa=\kappa.$$
--
--   Hessenberg proved this in 1906. It implies that $\kappa+\lambda=\kappa\cdot\lambda=\max(\kappa,\lambda)$ for infinite $\kappa$ and nonzero $\lambda$, which makes cardinal addition and multiplication trivial for infinite cardinals. The usual proof well-orders $\kappa\times\kappa$ by the maximum of the two coordinates.
--
--   **Formalization note.** Mathlib's `Cardinal.mul_eq_self`. Infiniteness is `Cardinal.aleph0 ≤ c`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Cardinal.mul_eq_self`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem hessenberg_cardinal_mul_self_6c {c : Cardinal} (hc : Cardinal.aleph0 ≤ c) : c * c = c := by sorry

end FamousTheorems
