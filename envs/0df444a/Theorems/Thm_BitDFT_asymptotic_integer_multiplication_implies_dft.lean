-- Prove2me | Theorems.Thm_BitDFT_asymptotic_integer_multiplication_implies_dft
-- name    : BitDFT.asymptotic_integer_multiplication_implies_dft
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-24T12:01:49.061989+00:00
-- url     : https://prove2.me/theorems/8266fdac-20fe-47b1-ae5c-3be59270b5b5
-- title:
--   Asymptotic multiplication bounds imply Fourier bounds
-- statement:
--   Assuming the existing IntMul.MulTimeBound predicate for an arbitrary real-valued function $g$, there exist one Fourier machine, $C>0$ and a threshold $N$. For all $n,b\ge1$ whose working precision $q=b+3\ell(n)+5$ is at least $N$, every encoded unit-disc vector is transformed with unnormalised absolute error below $2^{-b}$ and output magnitude at most $n$ within $C[g(nq)+ng(q)+q\ell(q)^2+nq]$ transitions. No monotonicity or growth assumption on $g$ is added.
-- source:
--   Harvey and van der Hoeven, Integer multiplication is at least as hard as matrix transposition (2025), https://arxiv.org/abs/2503.22848, Sections 2–3.4; BitDFT transfer specification (24 October 2026) for explicit binary conventions and derived end-to-end formulations. Derived corollary — existing asymptotic bounds.

import Definitions.Def_BitDFT_Numerics
import Definitions.Def_IntMul_HvdH_KronMul
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open BitDFT

theorem BitDFT.asymptotic_integer_multiplication_implies_dft
    (g : ℕ → ℝ) (hg : IntMul.MulTimeBound g) :
    ∃ A : IntMul.MultitapeTM, ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ,
      ∀ n b : ℕ, 1 ≤ n → 1 ≤ b → N ≤ guardPrecision n b →
        ∀ U : Fin n → ℤ × ℤ, vectorDisc (guardPrecision n b) U →
          ∃ V : Fin n → ℤ × ℤ,
            Computes A (requestedInput b U)
              (encVector (guardPrecision n b + IntMul.lg n + 1) V)
              (C * transferCost g n (guardPrecision n b)) ∧
            (∀ k, ‖value (guardPrecision n b) (V k)‖ ≤ n) ∧
            (∀ k, ‖value (guardPrecision n b) (V k) -
              dft (fun j => value (guardPrecision n b) (U j)) k‖ < ((2 : ℝ) ^ b)⁻¹) := by sorry
