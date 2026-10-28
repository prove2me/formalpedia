-- Prove2me | Theorems.Thm_BitDFT_fixed_point_multiplication
-- name    : BitDFT.fixed_point_multiplication
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-24T12:01:37.837715+00:00
-- url     : https://prove2.me/theorems/b11db77f-c8d4-41df-b7de-f6e1e6bb332e
-- title:
--   Lemma 2.1 — fixed-point multiplication on a bit machine
-- statement:
--   Given any actual binary multiplication machine with pointwise bound $T$, there exist one machine and a positive constant, uniform in $p\ge1$ and input pairs in the fixed-point unit disc. The machine computes their rounded complex product in at most $CT(p)$ transitions, returns a pair in the disc, and its error against any two unit-disc complex values is strictly below the sum of the two input errors plus two ulps. No scalar multiplication is supplied free of charge.
-- source:
--   Harvey and van der Hoeven, Integer multiplication is at least as hard as matrix transposition (2025), https://arxiv.org/abs/2503.22848, Sections 2–3.4; BitDFT transfer specification (24 October 2026) for explicit binary conventions and derived end-to-end formulations. Lemma 2.1 — fixed-point multiplication.

import Definitions.Def_BitDFT_Numerics
import Definitions.Def_IntMul_HvdH_KronMul
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open BitDFT

theorem BitDFT.fixed_point_multiplication (M : IntMul.MultitapeTM) (T : ℕ → ℝ)
    (hM : Multiplier M T) :
    ∃ A : IntMul.MultitapeTM, ∃ C : ℝ, 0 < C ∧
      ∀ (p : ℕ), 1 ≤ p → ∀ U V : ℤ × ℤ, inDisc p U → inDisc p V →
        ∃ W : ℤ × ℤ,
          Computes A (encNat p ++ encComplex (p + 1) U ++ encComplex (p + 1) V)
            (encComplex (p + 1) W) (C * T p) ∧
          W = roundPair p (value p U * value p V) ∧ inDisc p W ∧
          ∀ u v : ℂ, ‖u‖ ≤ 1 → ‖v‖ ≤ 1 →
            ulpError p W (u * v) < ulpError p U u + ulpError p V v + 2 := by sorry
