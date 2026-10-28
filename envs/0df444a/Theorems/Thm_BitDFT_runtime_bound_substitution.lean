-- Prove2me | Theorems.Thm_BitDFT_runtime_bound_substitution
-- name    : BitDFT.runtime_bound_substitution
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-24T12:01:54.717335+00:00
-- url     : https://prove2.me/theorems/94b533d3-b516-418b-9654-6920db9ac8cc
-- title:
--   Substitute any improved multiplication bound
-- statement:
--   If a correct multiplier has pointwise bound $T$ and $T(s)\le B(s)$ for all positive widths, there exists a Fourier machine satisfying the same unnormalised $2^{-b}$ accuracy guarantee with runtime at most $C[B(nq)+nB(q)+q\ell(q)^2+nq]$. The new bound $B$ need not be monotone, regular or computable.
-- source:
--   Harvey and van der Hoeven, Integer multiplication is at least as hard as matrix transposition (2025), https://arxiv.org/abs/2503.22848, Sections 2–3.4; BitDFT transfer specification (24 October 2026) for explicit binary conventions and derived end-to-end formulations. Derived corollary — runtime substitution.

import Definitions.Def_BitDFT_Numerics
import Definitions.Def_IntMul_HvdH_KronMul
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open BitDFT

theorem BitDFT.runtime_bound_substitution
    (M : IntMul.MultitapeTM) (T B : ℕ → ℝ) (hM : Multiplier M T)
    (hB : ∀ n, 1 ≤ n → T n ≤ B n) :
    ∃ A : IntMul.MultitapeTM, ∃ C : ℝ, 0 < C ∧
      ∀ n b : ℕ, 1 ≤ n → 1 ≤ b →
        ∀ U : Fin n → ℤ × ℤ, vectorDisc (guardPrecision n b) U →
          ∃ V : Fin n → ℤ × ℤ,
            Computes A (requestedInput b U)
              (encVector (guardPrecision n b + IntMul.lg n + 1) V)
              (C * transferCost B n (guardPrecision n b)) ∧
            (∀ k, ‖value (guardPrecision n b) (V k)‖ ≤ n) ∧
            (∀ k, ‖value (guardPrecision n b) (V k) -
              dft (fun j => value (guardPrecision n b) (U j)) k‖ < ((2 : ℝ) ^ b)⁻¹) := by sorry
