-- Prove2me | Theorems.Thm_D1Bound5_finitePolynomial_height_scalar
-- name    : D1Bound5.finitePolynomial_height_scalar
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:23:21.109993+00:00
-- url     : https://prove2.me/theorems/0cb63b8d-5c1f-4364-9442-210d1cb79a0a
-- title:
--   Finite Polynomial height scalar
-- statement:
--   A rational computation on the actual coefficient vector supplies the strict height margin for every T≥1000. This avoids weakening the constants by combining coordinatewise maxima from different rows.
-- source:
--   D1Bound5/FinitePolynomialHeight.lean, lines 51-72, SHA-256 0a57cf8e5e1b1bdad792f7fa018731c8a4bb1a5108b9cf615b3eb680734f76c5. Project: https://github.com/tomislav-math/d1-bound5-lean

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








theorem _root_.D1Bound5.finitePolynomial_height_scalar (k : ℕ) (v : Fin (k+1) → ℝ)
    (hv : ∀ ell, 0 ≤ v ell) (M T : ℝ) (hT : 1000 ≤ T)
    (hslack : (101/100 : ℝ)*(∑ ell, v ell/(1000 : ℝ)^(k-(ell : ℕ))) < M) :
    (101/100 : ℝ)*(∑ ell, v ell*T^(ell : ℕ)) < M*T^k := by sorry

end D1Bound5
end
