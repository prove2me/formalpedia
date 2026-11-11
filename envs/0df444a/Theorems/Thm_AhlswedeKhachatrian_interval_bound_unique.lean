-- Prove2me | Theorems.Thm_AhlswedeKhachatrian_interval_bound_unique
-- name    : AhlswedeKhachatrian.interval_bound_unique
-- status  : Open
-- author  : @parclytaxel
-- created : 2026-11-10T17:43:57.075188+00:00
-- url     : https://prove2.me/theorems/0ea2771c-5d59-40bc-b4c1-e6b8fba1446c
-- title:
--   Bound/uniqueness away from critical points
-- statement:
--   If `1 ≤ t ≤ k ≤ n`, `r ≤ k - t` and `n` lies in `interval k t r`, `frankl n k t r` is the unique maximal (n,k,t)-intersecting family up to isomorphism of the ground set. Setting `r = 0` gives the Erdős–Ko–Rado theorem as proved by Wilson.

import Definitions.Def_AhlswedeKhachatrian

namespace AhlswedeKhachatrian

open Finset

variable {n k t r : ℕ} {A : Family n}

/-- Ahlswede–Khachatrian theorem away from critical points.
Setting `r = 0` gives the Erdős–Ko–Rado theorem. -/
theorem interval_bound_unique (h₀ : 1 ≤ t ∧ t ≤ k ∧ k ≤ n ∧ r ≤ k - t)
    (h₁ : ↑n ∈ interval k t r) (hA : A.Sized k ∧ A.Inter t) :
    #A ≤ #(frankl n k t r) ∧ (#A = #(frankl n k t r) → A.PermutesTo (frankl n k t r)) := by
  sorry

end AhlswedeKhachatrian
