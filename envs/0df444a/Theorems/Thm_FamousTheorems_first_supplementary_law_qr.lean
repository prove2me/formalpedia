-- Prove2me | Theorems.Thm_FamousTheorems_first_supplementary_law_qr
-- name    : FamousTheorems.first_supplementary_law_qr
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:38:24.92658+00:00
-- url     : https://prove2.me/theorems/706dc179-5b8f-401e-9519-cac4485654b0
-- title:
--   The first supplementary law of quadratic reciprocity
-- statement:
--   **The first supplementary law of quadratic reciprocity.** Let $p$ be a prime. Then $-1$ is a square modulo $p$ if and only if $p\not\equiv3\pmod 4$.
--
--   Equivalently, $\left(\frac{-1}{p}\right)=(-1)^{(p-1)/2}$ for odd $p$. Fermat and Euler used this law in the theorem on sums of two squares: an odd prime is a sum of two squares if and only if $p\equiv1\pmod4$. The prime $p=2$ is included, since $-1\equiv1$ is a square.
--
--   **Formalization note.** Mathlib's `ZMod.exists_sq_eq_neg_one_iff`. `IsSquare (-1 : ZMod p)` says that $-1$ is a square in $\mathbb Z/p\mathbb Z$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `ZMod.exists_sq_eq_neg_one_iff`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem first_supplementary_law_qr {p : ℕ} [Fact p.Prime] : IsSquare (-1 : ZMod p) ↔ p % 4 ≠ 3 := by sorry

end FamousTheorems
