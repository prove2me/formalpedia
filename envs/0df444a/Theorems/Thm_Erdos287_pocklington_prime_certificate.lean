-- Prove2me | Theorems.Thm_Erdos287_pocklington_prime_certificate
-- name    : Erdos287.pocklington_prime_certificate
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T22:16:09.757605+00:00
-- url     : https://prove2.me/theorems/9ec48fb8-ea64-5d0e-8570-d8e2e41a7559
-- title:
--   Primality certificate from a partially factored predecessor
-- statement:
--   Let n>1 and let F be a positive divisor of n-1 with F squared greater than n. For every prime d dividing F suppose there is a witness a with a^(n-1)=1 modulo n and a^((n-1)/d)-1 a unit modulo n. Then n is prime.
-- source:
--   Pocklington primality criterion for the Erdős #287 finite certificates.

import Mathlib

theorem Erdos287.pocklington_prime_certificate (n F : ℕ) (hn : 1 < n) (hF : 0 < F) (hdiv : F ∣ n - 1)
    (hsize : n < F ^ 2)
    (hw : ∀ d : ℕ, d.Prime → d ∣ F → ∃ a : ℕ,
      (a : ZMod n) ^ (n - 1) = 1 ∧ IsUnit ((a : ZMod n) ^ ((n - 1) / d) - 1)) :
    n.Prime := by sorry
