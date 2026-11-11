-- Prove2me | Theorems.Thm_AhlswedeKhachatrian_critical_bound_unique
-- name    : AhlswedeKhachatrian.critical_bound_unique
-- status  : Open
-- author  : @parclytaxel
-- created : 2026-11-10T17:44:24.535102+00:00
-- url     : https://prove2.me/theorems/2aa2dd60-4987-4b7f-8cc7-8d567220edc0
-- title:
--   Bound/uniqueness at critical points
-- statement:
--   If `1 ≤ t ≤ k ≤ n`, `r ≤ k - t` and `n = threshold k t r` (a critical value), `frankl n k t r` and `frankl n k t (r + 1)` have the same cardinality and are the unique maximal (n,k,t)-intersecting families up to isomorphism of the ground set. The uniqueness does not apply at `t = 1` and `n = 2k`.

import Definitions.Def_AhlswedeKhachatrian

namespace AhlswedeKhachatrian

open Finset

variable {n k t r : ℕ} {A : Family n}

/-- Ahlswede–Khachatrian theorem at critical points.
There are many non-equivalent families with `t = 1, n = 2 * k`. -/
lemma critical_bound_unique (h₀ : 1 ≤ t ∧ t ≤ k ∧ k ≤ n ∧ r ≤ k - t)
    (h₁ : n = threshold k t r) (hA : A.Sized k ∧ A.Inter t) :
    #A ≤ #(frankl n k t r) ∧ (#A = #(frankl n k t r) → 1 < t ∨ 2 * k < n →
      A.PermutesTo (frankl n k t r) ∨ A.PermutesTo (frankl n k t (r + 1))) := by
  sorry

end AhlswedeKhachatrian
