-- Prove2me | solution 1 for fermat_little_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-12T06:20:58.015015+00:00
-- url     : https://prove2.me/submissions/68924b25-17fd-409f-808c-e3671d74e193

-- Template proof for fermat_little_p using ZMod + decide
-- Paste one at a time to the correct theorem

-- For fermat_little_2: change theorem_id and ZMod 2, x^2-x=0
-- For fermat_little_3: ZMod 3, x^3-x=0
-- etc.

import Mathlib.Data.Int.Basic
import Mathlib.Data.ZMod.Basic

theorem solution (a : ℤ) : (2 : ℤ) ∣ a ^ 2 - a := by
  have key : ∀ x : ZMod 2, x ^ 2 - x = 0 := by decide
  have h : ((a ^ 2 - a : ℤ) : ZMod 2) = 0 := by push_cast; exact key _
  rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
