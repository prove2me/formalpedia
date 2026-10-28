-- Prove2me | Theorems.Thm_BitDFT_packing_machine
-- name    : BitDFT.packing_machine
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-24T12:01:44.742008+00:00
-- url     : https://prove2.me/theorems/ca101db9-2630-451d-bbcf-f214c2bfaa0e
-- title:
--   Linear bit-time implementation of signed packing
-- statement:
--   There exists one machine packing every length-$r$ integer list with $r,p\ge1$ and coefficient magnitudes at most $2^p$ into base $2^{3p}$ within $Crp$ transitions. Its input and output are explicitly encoded binary strings. It computes the existing signed kpack expression; the runtime is measured by machine transitions, not a supplied preparation charge.
-- source:
--   Harvey and van der Hoeven, Integer multiplication is at least as hard as matrix transposition (2025), https://arxiv.org/abs/2503.22848, Sections 2–3.4; BitDFT transfer specification (24 October 2026) for explicit binary conventions and derived end-to-end formulations. Proposition 3.1 proof — linear packing.

import Definitions.Def_BitDFT_Numerics
import Definitions.Def_IntMul_HvdH_KronMul
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open BitDFT

theorem BitDFT.packing_machine :
    ∃ A : IntMul.MultitapeTM, ∃ C : ℝ, 0 < C ∧
      ∀ r p : ℕ, 1 ≤ r → 1 ≤ p → ∀ a : List ℤ, a.length = r →
        (∀ x ∈ a, |x| ≤ 2 ^ p) →
          Computes A (encNat r ++ encNat p ++ encList (p + 1) a)
            (encInt (3 * p * r + 1) (IntMul.HvdH.kpack (2 ^ (3 * p)) a))
            (C * ((r : ℝ) * p)) := by sorry
