-- Prove2me | Theorems.Thm_BitDFT_dft_stability
-- name    : BitDFT.dft_stability
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T12:22:16.986431+00:00
-- url     : https://prove2.me/theorems/6667c07c-2c17-48cf-a860-419c70115157
-- title:
--   Coordinatewise input stability of the ordinary DFT
-- statement:
--   Let $X,Y\in\mathbb C^n$ and suppose that $|X_j-Y_j|\le\delta$ for every coordinate. Then every coordinate of the ordinary, unnormalised DFT satisfies
--   $$|\operatorname{DFT}(X)_k-\operatorname{DFT}(Y)_k|\le n\delta.$$
--   The transform uses the negative-sign exponential convention. This estimate transfers accuracy guarantees for an encoded input to accuracy guarantees for an underlying vector. It has no computational or runtime hypothesis.
-- source:
--   Elementary consequence of the DFT definition and the triangle inequality; mission-specific unnormalised counterpart of Harvey–van der Hoeven 2025, equation (3.1), https://arxiv.org/html/2503.22848v1#S3.SS2

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

theorem BitDFT.dft_stability {n : ℕ} (X Y : Fin n → ℂ) (δ : ℝ)
    (h : ∀ j, ‖X j - Y j‖ ≤ δ) (k : Fin n) :
    ‖dft X k - dft Y k‖ ≤ (n : ℝ) * δ := by sorry
