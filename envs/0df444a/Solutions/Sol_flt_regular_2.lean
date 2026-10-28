-- Prove2me | solution 2 for flt_regular
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-25T19:38:42.391304+00:00
-- url     : https://prove2.me/submissions/f9c702d9-bd59-4c2f-96d6-1c1b2212cdb0

import Mathlib.NumberTheory.FLT.Basic
import Mathlib.NumberTheory.FLT.Three
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.ClassNumber
import Theorems.Thm_FreyPackage_fermatLastTheoremFor_of_five_le

open scoped NumberField

-- Shorter proof of FLT for regular primes: the conclusion follows from the
-- general theorem for prime exponents >= 5 (with the p = 3 case handled by
-- Mathlib's FLT for exponent 3), replacing the 4,252-line Kummer-style
-- development currently accepted for flt_regular.
theorem solution {p : ℕ} [Fact p.Prime]
    (hreg : p.Coprime (Fintype.card (ClassGroup (𝓞 (CyclotomicField p ℚ)))))
    (hodd : p ≠ 2) : FermatLastTheoremFor p := by
  have hp : p.Prime := Fact.out
  by_cases h3 : p = 3
  · subst h3
    show ∀ a b c : ℕ, a ≠ 0 → b ≠ 0 → c ≠ 0 → a ^ 3 + b ^ 3 ≠ c ^ 3
    intro a b c ha hb hc
    exact fermatLastTheoremThree a b c ha hb hc
  · have h5 : 5 ≤ p := by
      rcases hp.eq_two_or_odd with h | h
      · exact absurd h hodd
      · have h2 := hp.two_le
        omega
    exact FreyPackage.fermatLastTheoremFor_of_five_le p hp h5
