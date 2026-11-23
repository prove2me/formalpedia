-- Prove2me | Theorems.Thm_BroughanRH_nicolasPrimorial
-- name    : BroughanRH.nicolasPrimorial
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:13:20.866109+00:00
-- url     : https://prove2.me/theorems/99d93f4a-7e81-41ef-977c-3caf1b8288bd
-- title:
--   Nicolas’s primorial inequality
-- statement:
--   For each prime $p$, the product $n$ of the primes through $p$ satisfies $n/\varphi(n)>e^\gamma\log\log n$.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, I Thm. 5.31. https://doi.org/10.1017/9781108178228

import Mathlib

namespace BroughanRH

theorem nicolasPrimorial :
    ∀ p : ℕ, p.Prime →
      let n := primorial p
      (n : ℝ) / n.totient > Real.exp Real.eulerMascheroniConstant * Real.log (Real.log n) := by sorry

end BroughanRH
