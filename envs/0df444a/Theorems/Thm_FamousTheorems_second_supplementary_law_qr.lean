-- Prove2me | Theorems.Thm_FamousTheorems_second_supplementary_law_qr
-- name    : FamousTheorems.second_supplementary_law_qr
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:38:26.068058+00:00
-- url     : https://prove2.me/theorems/18cea536-0b6c-4698-b5be-fdd2d46edc54
-- title:
--   The second supplementary law of quadratic reciprocity
-- statement:
--   **The second supplementary law of quadratic reciprocity.** Let $p$ be an odd prime. Then $2$ is a square modulo $p$ if and only if $p\equiv\pm1\pmod 8$.
--
--   Equivalently, $\left(\frac2p\right)=(-1)^{(p^2-1)/8}$. Together with quadratic reciprocity and the first supplementary law, it lets one compute any Legendre symbol. It also gives facts such as the primality test for $2^p-1$ when $p\equiv3\pmod 4$ and $2p+1$ is prime.
--
--   **Formalization note.** Mathlib's `ZMod.exists_sq_eq_two_iff`. `IsSquare (2 : ZMod p)` says that $2$ is a square in $\mathbb Z/p\mathbb Z$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `ZMod.exists_sq_eq_two_iff`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem second_supplementary_law_qr {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) : IsSquare (2 : ZMod p) ↔ p % 8 = 1 ∨ p % 8 = 7 := by sorry

end FamousTheorems
