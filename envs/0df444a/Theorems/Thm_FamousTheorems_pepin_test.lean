-- Prove2me | Theorems.Thm_FamousTheorems_pepin_test
-- name    : FamousTheorems.pepin_test
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T02:04:29.737014+00:00
-- url     : https://prove2.me/theorems/303f5358-6495-41c8-871e-62fb7a04e83d
-- title:
--   Pépin's test (sufficiency)
-- statement:
--   **Pépin's test (sufficiency).** Let $F_n=2^{2^n}+1$ be the $n$-th Fermat number. If
--   $$3^{(F_n-1)/2}=3^{2^{2^n-1}}\equiv-1\pmod{F_n},$$
--   then $F_n$ is prime.
--
--   Pépin's test is the standard deterministic primality test for Fermat numbers. By quadratic reciprocity the converse also holds for $n\ge1$, but only the certifying direction is stated here. It has been used to prove $F_{14}$, $F_{20}$ and $F_{24}$ composite and to confirm $F_1,\dots,F_4$ prime.
--
--   **Formalization note.** Mathlib's `Nat.pepin_primality`. `Nat.fermatNumber n` is $2^{2^n}+1$ and the congruence is stated in `ZMod (Nat.fermatNumber n)`. The exponent $2^{2^n-1}$ equals $(F_n-1)/2$. The converse (necessity) is not part of this statement.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Nat.pepin_primality`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem pepin_test (n : ℕ) (h : (3 : ZMod n.fermatNumber) ^ 2 ^ (2 ^ n - 1) = -1) : n.fermatNumber.Prime := by sorry

end FamousTheorems
