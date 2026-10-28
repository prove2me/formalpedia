-- Prove2me | Theorems.Thm_BitDFT_unpacking_machine
-- name    : BitDFT.unpacking_machine
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-24T12:01:37.698544+00:00
-- url     : https://prove2.me/theorems/3a9d0791-96d8-4079-919b-de51b895da98
-- title:
--   Linear bit-time implementation of balanced-digit extraction
-- statement:
--   There exists one machine that, for $r,\beta\ge1$ and $|W|<2^{\beta r}$, computes the first $r$ balanced base-$2^\beta$ digits using the existing kunpack definition in $Cr\beta$ transitions. The remaining quotient is discarded; this primitive does not assert that arbitrary such inputs reconstruct from those digits. Kronecker correctness supplies reconstruction under its own spacing conditions.
-- source:
--   Harvey and van der Hoeven, Integer multiplication is at least as hard as matrix transposition (2025), https://arxiv.org/abs/2503.22848, Sections 2–3.4; BitDFT transfer specification (24 October 2026) for explicit binary conventions and derived end-to-end formulations. Proposition 3.1 proof — linear decoding.

import Definitions.Def_BitDFT_Numerics
import Definitions.Def_IntMul_HvdH_KronMul
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open BitDFT

theorem BitDFT.unpacking_machine :
    ∃ A : IntMul.MultitapeTM, ∃ C : ℝ, 0 < C ∧
      ∀ r β : ℕ, 1 ≤ r → 1 ≤ β → ∀ W : ℤ, W.natAbs < 2 ^ (β * r) →
        Computes A (encNat r ++ encNat β ++ encInt (β * r + 1) W)
          (encList (β + 1) (IntMul.HvdH.kunpack (2 ^ β) r W))
          (C * ((r : ℝ) * β)) := by sorry
