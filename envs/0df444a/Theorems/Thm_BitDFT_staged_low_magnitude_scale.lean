-- Prove2me | Theorems.Thm_BitDFT_staged_low_magnitude_scale
-- name    : BitDFT.staged_low_magnitude_scale
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T02:57:36.821245+00:00
-- url     : https://prove2.me/theorems/da4b06bc-8d5e-4408-80dc-642f88f2267c
-- title:
--   A staged q-bit call scales a magnitude below the boundary
-- statement:
--   Suppose a correct multiplier has q-bit runtime bound T(q), and its reusable caller has already been staged with the q-bit encodings of n and a, with a clean work bank. For n≥1, q≥ℓ(n)+1 and a<2^q, the complete caller run returns the exact product na, encoded in 2q bits and padded to the required q+ℓ(n)+1-bit output field. The run takes at most 6T(q)+14q+20 steps. The boundary a=2^q is handled by the separate exact high-bit branch.
-- source:
--   Composition of the accepted staged q-bit multiplier call with the exact low-magnitude arithmetic and serialization theorem. It isolates the below-boundary coordinate operation required by the repeated output-scaling controller.

import Theorems.Thm_BitDFT_staged_qbit_product
import Theorems.Thm_BitDFT_scalar_scaled_word_complete_v2
import Definitions.Def_IntMul_TrackedBankedCall
import Mathlib.Tactic
set_option autoImplicit false
open IntMul BitDFT
open IntMul.TrackedBankPreparation (inputWord)

theorem BitDFT.staged_low_magnitude_scale (M : MultitapeTM) (T : ℕ → ℝ) (hM : Multiplier M T)
    (q n a : ℕ) (hn : 1 ≤ n) (hq : lg n + 1 ≤ q)
    (hnwide : n ≤ 2^(lg n)) (ha : a < 2^q)
    (base : (TrackedBankedCall.machine M).Cfg)
    (hs : base.state = (TrackedBankedCall.machine M).qStart)
    (hbuf : base.cells (TrackedBankedCall.machine M).outTape =
      (TrackedBankedCall.machine M).tapeOf
        ((TrackedBankedCall.machine M).blank ::
          (inputWord M (bin q n) (bin q a)).map (fun s => some (s, true))))
    (hh : base.head (TrackedBankedCall.machine M).outTape = 1)
    (hwork : ∀ i : Fin (M.k + 2), 2 ≤ i.val →
      base.cells i = (TrackedBankedCall.machine M).tapeOf [] ∧ base.head i = 1) :
    ∃ t tm : ℕ,
      (tm : ℝ) ≤ T q ∧
      (t : ℝ) ≤ 6 * T q + 14 * q + 20 ∧
      (TrackedBankedCall.machine M).step^[t] base =
        TrackedBankedCall.finalFrame M base 1 (fun _ => 1)
          (TrackedBankedSimulation.extents M (M.initCfg (bin q n) (bin q a))
            (TrackedBankPreparation.initialExtent M (bin q n) (bin q a)) tm)
          (M.step^[tm] (M.initCfg (bin q n) (bin q a)))
          (bin (2*q) (n*a)) ∧
      bin (2*q) (n*a) =
        List.replicate (2*q-(q+lg n+1)) false ++ bin (q+lg n+1) (n*a) := by sorry
