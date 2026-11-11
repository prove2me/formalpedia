-- Prove2me | Theorems.Thm_AhlswedeKhachatrian_four_n
-- name    : AhlswedeKhachatrian.four_n
-- status  : Open
-- author  : @parclytaxel
-- created : 2026-11-10T17:44:44.86446+00:00
-- url     : https://prove2.me/theorems/1c2291eb-cb63-44cf-8bc8-aba9be7f213a
-- title:
--   The 4n conjecture
-- statement:
--   The maximum size of a (4n,2n,2)-intersecting family is $\frac12(\binom{4n}{2n}-\binom{2n}n^2)$.

import Definitions.Def_AhlswedeKhachatrian

namespace AhlswedeKhachatrian

open Finset

lemma four_n {n : ℕ} {A : Family (4 * n)} (hA : A.Sized (2 * n) ∧ A.Inter 2) :
    2 * #A ≤ (4 * n).choose (2 * n) - (2 * n).choose n ^ 2 := by
  sorry

end AhlswedeKhachatrian
