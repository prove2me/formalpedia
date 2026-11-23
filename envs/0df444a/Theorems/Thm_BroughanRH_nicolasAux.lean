-- Prove2me | Theorems.Thm_BroughanRH_nicolasAux
-- name    : BroughanRH.nicolasAux
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:18:01.32073+00:00
-- url     : https://prove2.me/theorems/b2de4fc3-a23f-4d8f-8a53-1b848565539c
-- title:
--   Nicolas’s inequality in Chebyshev coordinates
-- statement:
--   For $x\ge2$, the product $e^\gamma\log(\vartheta(x))\prod_{p\le x}(1-1/p)$ is strictly less than one.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, I Thm. 5.31 (function form). https://doi.org/10.1017/9781108178228

import Mathlib

namespace BroughanRH

theorem nicolasAux :
    ∀ x : ℝ, 2 ≤ x → Real.exp Real.eulerMascheroniConstant * Real.log (Chebyshev.theta x) * (∏ p ∈ (Finset.Icc 2 ⌊x⌋₊).filter Nat.Prime, (1 - 1/(p : ℝ))) < 1 := by sorry

end BroughanRH
