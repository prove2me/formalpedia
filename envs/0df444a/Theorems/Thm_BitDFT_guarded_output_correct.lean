-- Prove2me | Theorems.Thm_BitDFT_guarded_output_correct
-- name    : BitDFT.guarded_output_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T12:22:23.351156+00:00
-- url     : https://prove2.me/theorems/c0ae9312-2f14-4935-a632-33c2f4ec9370
-- title:
--   Guard precision converts a normalized DFT error to absolute error
-- statement:
--   Let $n\ge1$, $b\ge0$, and $q=b+3\ell(n)+5$, with $\ell(n)=\max(1,\lceil\log_2 n\rceil)$. Suppose a precision-$q$ dyadic vector $W$ lies in the unit disc and approximates the normalized DFT of $X$ with error less than $12n^2$ ulps. Multiplying the integer components of $W$ by $n$, while keeping the denominator $2^q$, gives a vector $V$ satisfying
--   $$|V_k|\le n,\qquad |V_k-\operatorname{DFT}(X)_k|<2^{-b}.$$
--   This is a numerical statement about exact integer scaling; it does not assume or assert a machine runtime.
-- source:
--   Original guard-precision corollary of the normalized error bound in Harvey–van der Hoeven 2025, Proposition 3.3, https://arxiv.org/html/2503.22848v1#S3.SS4; numerical derivation in transfer-proof.tex, Conversion to the mission’s ordinary DFT.

import Definitions.Def_BitDFT_Numerics
import Theorems.Thm_BitDFT_guard_precision_bound
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open BitDFT

theorem BitDFT.guarded_output_correct (n b : ℕ) (hn : 1 ≤ n)
    (X : Fin n → ℂ) (W : Fin n → ℤ × ℤ)
    (hdisc : vectorDisc (guardPrecision n b) W)
    (herr : ∀ k, ulpError (guardPrecision n b) (W k) (ndft X k) < 12 * (n : ℝ)^2) :
    (∀ k, ‖value (guardPrecision n b) ((n : ℤ) * (W k).1, (n : ℤ) * (W k).2)‖ ≤ n) ∧
    (∀ k, ‖value (guardPrecision n b) ((n : ℤ) * (W k).1, (n : ℤ) * (W k).2) - dft X k‖ < ((2 : ℝ)^b)⁻¹) := by sorry
