-- Prove2me | Theorems.Thm_BitDFT_constant_factor_multiplication
-- name    : BitDFT.constant_factor_multiplication
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-24T12:01:36.423503+00:00
-- url     : https://prove2.me/theorems/faf26120-1f4d-4de7-95ac-18a0b2965f02
-- title:
--   Lemma 3.2 — adapt a multiplier to larger operands
-- statement:
--   For any positive integer $L$ and multiplier with bound $T$, there is a uniform machine multiplying two $s$-bit inputs in $CT(m)$ transitions whenever $m,s\ge1$ and $s\le Lm$. Both widths are supplied in the input. No inequality between $T(Lm)$ and $T(m)$ is assumed.
-- source:
--   Harvey and van der Hoeven, Integer multiplication is at least as hard as matrix transposition (2025), https://arxiv.org/abs/2503.22848, Sections 2–3.4; BitDFT transfer specification (24 October 2026) for explicit binary conventions and derived end-to-end formulations. Lemma 3.2 — constant-factor size adaptation.

import Definitions.Def_BitDFT_Numerics
import Definitions.Def_IntMul_HvdH_KronMul
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open BitDFT

theorem BitDFT.constant_factor_multiplication (L : ℕ) (hL : 1 ≤ L)
    (M : IntMul.MultitapeTM) (T : ℕ → ℝ) (hM : Multiplier M T) :
    ∃ A : IntMul.MultitapeTM, ∃ C : ℝ, 0 < C ∧
      ∀ m s : ℕ, 1 ≤ m → 1 ≤ s → s ≤ L * m →
        ∀ x y : List Bool, x.length = s → y.length = s →
          Computes A (encNat m ++ encNat s ++ x ++ y)
            (IntMul.bin (2 * s) (IntMul.val x * IntMul.val y)) (C * T m) := by sorry
