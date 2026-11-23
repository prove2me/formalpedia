-- Prove2me | Theorems.Thm_BroughanRH_nicolasMin
-- name    : BroughanRH.nicolasMin
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:16:50.25981+00:00
-- url     : https://prove2.me/theorems/e776d064-2e17-4349-818e-6dae8db3754f
-- title:
--   The lower bound along primorials
-- statement:
--   On primorials the normalized totient error is at least its value at $2$.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, I Thm. 5.34 (4). https://doi.org/10.1017/9781108178228

import Mathlib

namespace BroughanRH

theorem nicolasMin :
    let c (n : ℕ) : ℝ := ((n : ℝ) / (n.totient : ℝ) - Real.exp Real.eulerMascheroniConstant * Real.log (Real.log n)) * Real.sqrt (Real.log n)
    ∀ p : ℕ, p.Prime → c 2 ≤ c (primorial p) := by sorry

end BroughanRH
