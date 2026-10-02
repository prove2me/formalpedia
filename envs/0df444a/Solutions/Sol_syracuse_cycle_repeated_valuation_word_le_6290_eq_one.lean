-- Prove2me | solution 1 for syracuse_cycle_repeated_valuation_word_le_6290_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @FakeMink
-- created : 2026-10-01T17:57:40.221908+00:00
-- url     : https://prove2.me/submissions/1004a3ac-de76-4c64-a968-ec65e253fd17

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_valuation_word_rotation_rigidity
import Theorems.Thm_syracuse_period_le_6290_eq_one

set_option autoImplicit false

theorem solution (m p d : ℕ)
    (hm : 0 < m) (hp : 0 < p) (hd : 0 < d) (hdle : d ≤ 6290)
    (hcyc : syracuseStep^[p] m = m)
    (hword : ∀ i : ℕ, i < p →
      (3 * syracuseStep^[i + d] m + 1).factorization 2 =
        (3 * syracuseStep^[i] m + 1).factorization 2) :
    m = 1 := by
  have hreturn : syracuseStep^[d] m = m :=
    syracuse_valuation_word_rotation_rigidity m p d hm hp hcyc hword
  exact syracuse_period_le_6290_eq_one m d hm hd hdle hreturn

#print axioms solution
