-- Prove2me | Theorems.Thm_DetDLP_f6a_small_z_readout_poly
-- name    : DetDLP.f6a_small_z_readout_poly
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T03:07:47.642066+00:00
-- url     : https://prove2.me/theorems/ef9b0a3a-d2a6-41a2-854a-82eb4988dba3
-- title:
--   Polynomial-time readout of packed coefficients
-- statement:
--   The packed coefficient readout runs in polynomial time on four input words. For binary encodings of the integer, its radix and its reduction modulus, the fourth word specifies how many digits to return by its length. The output is the binary list encoding of the radix digits in increasing index order, each reduced modulo the given power of two.
-- source:
--   Solutions/M14A_small_kernel.lean, output coefficient formula of theorem solution.

import Mathlib
import Definitions.Def_DetDLP_F6AReadout
open DetDLP Groundwork DetDLP.F6AReadout

theorem DetDLP.f6a_small_z_readout_poly : PolyT readout ∧ ∀ (z w P : ℕ) (u : List Bool),
    readout (z.bits, (2^w : ℕ).bits, (2^P : ℕ).bits, u) =
      encodeNatListBin (List.ofFn fun i : Fin u.length => z / (2^w)^i.val % (2^w) % (2^P)) := by sorry
