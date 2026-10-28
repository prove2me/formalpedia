-- Prove2me | Theorems.Thm_D1Bound5_finitePolynomial_norm_le
-- name    : D1Bound5.finitePolynomial_norm_le
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:43:46.42886+00:00
-- url     : https://prove2.me/theorems/6da1bd70-4ac3-41f0-b4cf-81c8eba23970
-- title:
--   Finite Polynomial norm le
-- statement:
--   Auxiliary result `finitePolynomial_norm_le` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/FinitePolynomialHeight.lean, lines 9-14, SHA-256 0a57cf8e5e1b1bdad792f7fa018731c8a4bb1a5108b9cf615b3eb680734f76c5. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section
namespace D1Bound5

theorem _root_.D1Bound5.finitePolynomial_norm_le (k : ℕ) (a : Fin (k+1) → ℂ) (c : ℂ) :
    ‖∑ ell, a ell*c^(ell : ℕ)‖ ≤ ∑ ell, ‖a ell‖*‖c‖^(ell : ℕ) := by sorry







end D1Bound5
end
