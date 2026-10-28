-- Prove2me | Theorems.Thm_BitDFT_clean_multiplier_call
-- name    : BitDFT.clean_multiplier_call
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T13:34:52.98871+00:00
-- url     : https://prove2.me/theorems/c314a1a2-ea51-4670-85f5-83d1cd21bdfd
-- title:
--   Any multiplier admits a clean work-tape call within 36 times its original bound
-- statement:
--   For every correct multiplier M on positive width s with time bound T, the existing tracked native-call compiler produces exactly the same 2s output bits within 36T actual transitions. At termination every simulated work-tape cell at a positive address is blank, and every simulated head is parked at cell one. The constant includes argument copying, simulation, output placement and workspace clearing. It does not assume monotonicity or regularity of the original running-time bound. This is a one-call compiler guarantee; assembling a complete Fourier program remains a separate theorem.
-- source:
--   Derived from IntMul.TrackedNativeCall.call_correct (https://prove2.me/theorems/3aabbbf5-10c7-4cc5-be9c-0616d0113e9e) and BitDFT.output_length_le_time (https://prove2.me/theorems/32b8b632-fa91-4c36-aefc-c919a87a4acc). The new explicit constant follows by bounding tracked extents by input length plus elapsed time. This formalizes the reusable finite-tape multiplier-call overhead needed in the BitDFT reduction.

import Definitions.Def_IntMul_TrackedNativeCall
import Definitions.Def_BitDFT_Encoding
open IntMul

theorem BitDFT.clean_multiplier_call (M : MultitapeTM) (s : ℕ) (T : ℝ)
    (hs : 1 ≤ s) (hM : MultipliesAt M s T) :
    ∀ x y : List Bool, x.length = s → y.length = s →
    ∃ t : ℕ, (t : ℝ) ≤ 36 * T ∧
      (IntMul.TrackedNativeCall.machine M).HaltsWithOutput x y t
        (IntMul.bin (2 * s) (IntMul.val x * IntMul.val y)) ∧
      (∀ j p, 1 ≤ p →
        ((IntMul.TrackedNativeCall.machine M).step^[t]
          ((IntMul.TrackedNativeCall.machine M).initCfg x y)).cells
          (IntMul.BankedSimulation.workTape M j) p = some (M.blank, false)) ∧
      (∀ j, ((IntMul.TrackedNativeCall.machine M).step^[t]
        ((IntMul.TrackedNativeCall.machine M).initCfg x y)).head
          (IntMul.BankedSimulation.workTape M j) = 1) := by sorry
