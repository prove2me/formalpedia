-- Prove2me | solution 2 for fermat_last_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-03T11:26:24.190474+00:00
-- url     : https://prove2.me/submissions/f89ce7b9-3184-4a55-8973-b6d75e83967c

import Mathlib.NumberTheory.FLT.Three
import Mathlib.NumberTheory.FLT.Four
import Theorems.Thm_FreyPackage_fermatLastTheoremFor_of_five_le

set_option autoImplicit false

-- Connect the mission directly to the prime-exponent input.
theorem solution (n : ℕ) (hn : 3 ≤ n) (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a ^ n + b ^ n ≠ c ^ n := by
  have hFLT : FermatLastTheorem := FermatLastTheorem.of_odd_primes <| by
    intro p hp hodd
    by_cases h3 : p = 3
    · simpa only [h3] using fermatLastTheoremThree
    · apply FreyPackage.fermatLastTheoremFor_of_five_le p hp
      obtain ⟨k, hk⟩ := hodd
      have h2 := hp.two_le
      omega
  exact hFLT n hn a b c ha.ne' hb.ne' hc.ne'
