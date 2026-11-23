-- Prove2me | Theorems.Thm_BroughanRH_nicolasLimsup
-- name    : BroughanRH.nicolasLimsup
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:13:35.420711+00:00
-- url     : https://prove2.me/theorems/6fbff7bd-a9d7-469c-b353-70b04b115aea
-- title:
--   Nicolas’s limiting upper value
-- statement:
--   The limit superior of the normalized totient error is $e^\gamma(2+\beta)$, where $\beta=2+\gamma-\log\pi-2\log 2$.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, I Thm. 5.34 (1). https://doi.org/10.1017/9781108178228

import Mathlib

namespace BroughanRH

theorem nicolasLimsup :
    let c (n : ℕ) : ℝ := ((n : ℝ) / (n.totient : ℝ) - Real.exp Real.eulerMascheroniConstant * Real.log (Real.log n)) * Real.sqrt (Real.log n)
    let β : ℝ := 2 + Real.eulerMascheroniConstant - Real.log Real.pi - 2 * Real.log 2
    Filter.limsup (fun n : ℕ => (c n : EReal)) Filter.atTop = ((Real.exp Real.eulerMascheroniConstant * (2 + β) : ℝ) : EReal) := by sorry

end BroughanRH
