-- Prove2me | solution 1 for flt_three
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-11T17:27:42.406406+00:00
-- url     : https://prove2.me/submissions/fbc4a353-b59e-4f4f-9a1e-ae83604197e4

import Mathlib.NumberTheory.FLT.Three
import Mathlib.Data.Nat.Basic

theorem solution (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 :=
  fermatLastTheoremThree a b c (by omega) (by omega) (by omega)
