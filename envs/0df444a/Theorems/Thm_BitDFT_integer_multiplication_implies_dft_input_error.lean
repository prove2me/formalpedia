-- Prove2me | Theorems.Thm_BitDFT_integer_multiplication_implies_dft_input_error
-- name    : BitDFT.integer_multiplication_implies_dft_input_error
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-24T12:01:35.406004+00:00
-- url     : https://prove2.me/theorems/5d1769fe-c98f-4a19-943a-e0c847e13597
-- title:
--   End-to-end transfer with input approximation error
-- statement:
--   The same existential machine and runtime conclusion can be achieved with this stronger guarantee: for every exact complex input approximated by the encoded vector with coordinatewise error at most $\delta$, the unnormalised output error is strictly below $n\delta+2^{-b}$. The encoded input lies in the unit disc; the compared exact input need not. The output and runtime quantifiers precede the exact input and error tolerance.
-- source:
--   Harvey and van der Hoeven, Integer multiplication is at least as hard as matrix transposition (2025), https://arxiv.org/abs/2503.22848, Sections 2–3.4; BitDFT transfer specification (24 October 2026) for explicit binary conventions and derived end-to-end formulations. Derived corollary — input error propagation.

import Definitions.Def_BitDFT_Numerics
import Definitions.Def_IntMul_HvdH_KronMul
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open BitDFT

theorem BitDFT.integer_multiplication_implies_dft_input_error
    (M : IntMul.MultitapeTM) (T : ℕ → ℝ) (hM : Multiplier M T) :
    ∃ A : IntMul.MultitapeTM, ∃ C : ℝ, 0 < C ∧
      ∀ n b : ℕ, 1 ≤ n → 1 ≤ b →
        ∀ U : Fin n → ℤ × ℤ, vectorDisc (guardPrecision n b) U →
          ∃ V : Fin n → ℤ × ℤ,
            Computes A (requestedInput b U)
              (encVector (guardPrecision n b + IntMul.lg n + 1) V)
              (C * transferCost T n (guardPrecision n b)) ∧
            (∀ k, ‖value (guardPrecision n b) (V k)‖ ≤ n) ∧
            ∀ (X : Fin n → ℂ) (δ : ℝ),
              (∀ j, ‖value (guardPrecision n b) (U j) - X j‖ ≤ δ) →
              ∀ k, ‖value (guardPrecision n b) (V k) - dft X k‖ <
                (n : ℝ) * δ + ((2 : ℝ) ^ b)⁻¹ := by sorry
