-- Prove2me | Theorems.Thm_BitDFT_integer_multiplication_implies_dft
-- name    : BitDFT.integer_multiplication_implies_dft
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-24T12:01:54.614466+00:00
-- url     : https://prove2.me/theorems/b07bb6a9-8860-4ac5-aec7-9cfb29c46fda
-- title:
--   General integer multiplication to approximate DFT transfer
-- statement:
--   For any binary multiplication machine with a pointwise runtime bound $T$ at every positive bit width, there exist one multitape Fourier machine and a constant $C>0$. For every $n,b\ge1$ and any unit-disc input encoded at $q=b+3\ell(n)+5$ bits of precision, the machine returns an encoded approximation to the ordinary unnormalised negative-sign DFT. Every output has magnitude at most $n$ and absolute error strictly below $2^{-b}$. Runtime is at most $C[T(nq)+nT(q)+q\ell(q)^2+nq]$ actual transitions. Encoding, root construction, rounding and output costs are inside this bound. No Fourier oracle, preparation-cost hypothesis or regularity assumption on $T$ is present.
-- source:
--   Harvey and van der Hoeven, Integer multiplication is at least as hard as matrix transposition (2025), https://arxiv.org/abs/2503.22848, Sections 2–3.4; BitDFT transfer specification (24 October 2026) for explicit binary conventions and derived end-to-end formulations. Main transfer theorem.

import Definitions.Def_BitDFT_Numerics
import Definitions.Def_IntMul_HvdH_KronMul
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open BitDFT

theorem BitDFT.integer_multiplication_implies_dft
    (M : IntMul.MultitapeTM) (T : ℕ → ℝ) (hM : Multiplier M T) :
    ∃ A : IntMul.MultitapeTM, ∃ C : ℝ, 0 < C ∧
      ∀ n b : ℕ, 1 ≤ n → 1 ≤ b →
        ∀ U : Fin n → ℤ × ℤ, vectorDisc (guardPrecision n b) U →
          ∃ V : Fin n → ℤ × ℤ,
            Computes A (requestedInput b U)
              (encVector (guardPrecision n b + IntMul.lg n + 1) V)
              (C * transferCost T n (guardPrecision n b)) ∧
            (∀ k, ‖value (guardPrecision n b) (V k)‖ ≤ n) ∧
            (∀ k, ‖value (guardPrecision n b) (V k) -
              dft (fun j => value (guardPrecision n b) (U j)) k‖ < ((2 : ℝ) ^ b)⁻¹) := by sorry
