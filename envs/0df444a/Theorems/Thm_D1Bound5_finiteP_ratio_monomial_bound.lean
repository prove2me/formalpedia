-- Prove2me | Theorems.Thm_D1Bound5_finiteP_ratio_monomial_bound
-- name    : D1Bound5.finiteP_ratio_monomial_bound
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:32:28.167211+00:00
-- url     : https://prove2.me/theorems/dd339402-c2e1-466e-aaf7-5dbb7793450d
-- title:
--   Finite P ratio monomial bound
-- statement:
--   The ratio-sensitive monomial bound used by the finite P rows. The exponent certificates are checked on the actual finite coefficient tables. No analytic or polynomial-height bound occurs as a hypothesis.
-- source:
--   D1Bound5/FinitePRatioMonomial.lean, lines 7-71, SHA-256 b645ae319051e493e06ab3f189ab35141a10b30a61417e013dd7c4ae06dcbe00. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

section
namespace D1Bound5


theorem _root_.D1Bound5.finiteP_ratio_monomial_bound (A B S : ℝ)
    (hA : 1 ≤ A) (hAB : A ≤ B) (hBS : B ≤ S)
    (r : Fin 3) (i j l m t e : ℕ)
    (htotal : i+j+l+t ≤ m+2)
    (he : e+j+l = if r=0 then 2 else m+2)
    (hl : r ≠ 2 → l ≤ 2) :
    A^i*B^j*S^l/(![A,B,S] r)^m ≤ (S^2/A^t)*(A/B)^e := by sorry

end D1Bound5
end
