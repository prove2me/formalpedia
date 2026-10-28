-- Prove2me | Theorems.Thm_D1Bound5_finite_eta_reciprocal_lt
-- name    : D1Bound5.finite_eta_reciprocal_lt
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:47:36.440074+00:00
-- url     : https://prove2.me/theorems/9e38248d-205e-45e2-a59d-247563e28880
-- title:
--   Finite eta reciprocal lt
-- statement:
--   Auxiliary result `finite_eta_reciprocal_lt` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/FiniteEtaBound.lean, lines 26-30, SHA-256 bbe0c480ef14e08f89c2bfd31afb3f5e0e4f98178a555879f1db7d5985f98cf6. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

section
namespace D1Bound5



theorem _root_.D1Bound5.finite_eta_reciprocal_lt (T e : ℝ) (hT : 1000 ≤ T) (he : e ≤ 9) :
    1/(1-1/T)^e < (101/100 : ℝ) := by sorry

end D1Bound5
end
