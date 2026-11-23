-- Prove2me | Theorems.Thm_BroughanRH_matiyasevichWitness
-- name    : BroughanRH.matiyasevichWitness
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:28:52.155193+00:00
-- url     : https://prove2.me/theorems/25d03e60-b256-4977-b8bb-00e849ea3ca6
-- title:
--   Absence of Matiyasevich’s first-order counterexamples
-- statement:
--   The first-order counterexample conditions have no positive-integer solution. The least-common-multiple condition is written directly as specified in the theorem’s proof. This resolves the reversed quantifier guard in the printed clause (M3).
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, III Thm. 11.1. https://doi.org/10.1017/9781009384780

import Mathlib

namespace BroughanRH

theorem matiyasevichWitness :
    let M (a b : ℕ) := ∃ x : ℕ, b+1 < x ∧
      (x+1)^(x*b) ≤ (a+1)*x^(x*b) ∧ (a+1)*x^(x*b) < 4*(x+1)^(x*b)
    ¬ ∃ k l m n : ℕ, 0 < k ∧ 0 < l ∧ 600 ≤ n ∧
      m = (Finset.Icc 1 n).lcm id ∧
      (4*n*k^4 : ℕ) < (Int.natAbs ((l : ℤ) - (n : ℤ)))^2 ∧
      M (m-1) l ∧ M (n-1) k := by sorry

end BroughanRH
