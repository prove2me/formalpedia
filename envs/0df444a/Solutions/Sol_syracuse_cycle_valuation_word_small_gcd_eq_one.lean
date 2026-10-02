-- Prove2me | solution 1 for syracuse_cycle_valuation_word_small_gcd_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @FakeMink
-- created : 2026-10-01T18:57:20.626986+00:00
-- url     : https://prove2.me/submissions/61262bff-e04a-42c3-b2ac-2809a77d28d3

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_valuation_word_rotation_rigidity
import Theorems.Thm_syracuse_period_le_6290_eq_one

set_option autoImplicit false

namespace CollatzSyracuseWordGcdReductionDraft01

theorem word_symmetry_gcd_return (m p d : ℕ)
    (hm : 0 < m) (hp : 0 < p)
    (hcyc : syracuseStep^[p] m = m)
    (hword : ∀ i : ℕ, i < p →
      (3 * syracuseStep^[i + d] m + 1).factorization 2 =
        (3 * syracuseStep^[i] m + 1).factorization 2) :
    syracuseStep^[Nat.gcd p d] m = m := by
  have hreturn : syracuseStep^[d] m = m :=
    syracuse_valuation_word_rotation_rigidity m p d hm hp hcyc hword
  exact Function.IsPeriodicPt.gcd hcyc hreturn

theorem word_symmetry_small_gcd_eq_one (m p d : ℕ)
    (hm : 0 < m) (hp : 0 < p) (hg : Nat.gcd p d ≤ 6290)
    (hcyc : syracuseStep^[p] m = m)
    (hword : ∀ i : ℕ, i < p →
      (3 * syracuseStep^[i + d] m + 1).factorization 2 =
        (3 * syracuseStep^[i] m + 1).factorization 2) :
    m = 1 := by
  exact syracuse_period_le_6290_eq_one m (Nat.gcd p d) hm
    (Nat.gcd_pos_of_pos_left d hp) hg
    (word_symmetry_gcd_return m p d hm hp hcyc hword)

end CollatzSyracuseWordGcdReductionDraft01

theorem solution (m p d : ℕ)
    (hm : 0 < m) (hp : 0 < p) (hg : Nat.gcd p d ≤ 6290)
    (hcyc : syracuseStep^[p] m = m)
    (hword : ∀ i : ℕ, i < p →
      (3 * syracuseStep^[i + d] m + 1).factorization 2 =
        (3 * syracuseStep^[i] m + 1).factorization 2) :
    m = 1 := by
  exact CollatzSyracuseWordGcdReductionDraft01.word_symmetry_small_gcd_eq_one
    m p d hm hp hg hcyc hword

#print axioms solution
