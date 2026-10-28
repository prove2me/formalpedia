-- Prove2me | Theorems.Thm_D1Bound5_finitePolynomial_two_columns_norm_le
-- name    : D1Bound5.finitePolynomial_two_columns_norm_le
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:20:42.006384+00:00
-- url     : https://prove2.me/theorems/9c99a579-5bb5-4017-9a63-6f686a1518b1
-- title:
--   Finite Polynomial two columns norm le
-- statement:
--   Auxiliary result `finitePolynomial_two_columns_norm_le` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/FinitePolynomialHeight.lean, lines 16-39, SHA-256 0a57cf8e5e1b1bdad792f7fa018731c8a4bb1a5108b9cf615b3eb680734f76c5. Project: https://github.com/tomislav-math/d1-bound5-lean

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



theorem _root_.D1Bound5.finitePolynomial_two_columns_norm_le (k d0 : ℕ)
    (p : Fin 2 → Fin (k+1) → ℂ) (v : Fin (k+1) → ℝ) (c : ℂ) (Y : ℝ)
    (hcoeff : ∀ ell, ‖p 0 ell‖+‖p 1 ell‖ ≤ v ell*Y^(d0+(ell : ℕ))) :
    ‖∑ ell, p 0 ell*c^(ell : ℕ)‖+‖∑ ell, p 1 ell*c^(ell : ℕ)‖ ≤
      Y^d0*∑ ell, v ell*(Y*‖c‖)^(ell : ℕ) := by sorry





end D1Bound5
end
