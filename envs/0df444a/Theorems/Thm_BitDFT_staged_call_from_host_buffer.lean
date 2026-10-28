-- Prove2me | Theorems.Thm_BitDFT_staged_call_from_host_buffer
-- name    : BitDFT.staged_call_from_host_buffer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T19:22:52.69398+00:00
-- url     : https://prove2.me/theorems/3ae79595-c4d3-43ad-a46c-caa0172d2fa1
-- title:
--   A staged host buffer starts the tracked multiplier call
-- statement:
--   Let a multiplier M be embedded into a shared host alphabet. Suppose a host configuration has the tagged operand pair already written on the routed output buffer, its head at cell one, and every routed multiplier work tape blank with its head at cell one. Then decoding those routed tapes gives a caller frame from which the verified tracked multiplier call runs on the operands and returns the multiplier output. The resulting runtime is bounded by the multiplier's actual run, the visited work-bank span, and the linear operand-staging overhead.
-- source:
--   Projects the exact host buffer and blank multiplier work bank through the alphabet embedding to the tracked caller frame, then reuses the accepted staged_call_run theorem. The shared root input remains whatever the host frame supplied.

import Definitions.Def_IntMul_TrackedBankedCall
import Definitions.Def_BitDFT_AlphabetEmbedding
import Theorems.Thm_BitDFT_staged_call_run
import Mathlib.Data.List.GetD
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
open IntMul BitDFT

theorem BitDFT.staged_call_from_host_buffer (M N : MultitapeTM)
    (e : AlphabetEmbedding.Map (TrackedBankedCall.machine M) N)
    (route : Fin (TrackedBankedCall.machine M).k → Fin N.k)
    (c : N.Cfg) (x y : List Bool)
    (hbuffer : c.cells (route (TrackedBankedCall.machine M).outTape) =
      N.tapeOf (e.encode (TrackedBankedCall.machine M).blank ::
        (TrackedBankPreparation.inputWord M x y).map
          (fun s => e.encode (some (s, true)))))
    (hhead : c.head (route (TrackedBankedCall.machine M).outTape) = 1)
    (hwork : ∀ i : Fin (M.k + 2), 2 ≤ i.val →
      c.cells (route i) = N.tapeOf [] ∧ c.head (route i) = 1)
    (T : ℕ) (halt : (M.step^[T] (M.initCfg x y)).state = M.qHalt)
    (w : List Bool)
    (hout : (M.step^[T] (M.initCfg x y)).cells M.outTape =
      M.tapeOf (w.map M.bitSym)) :
    ∃ base : (TrackedBankedCall.machine M).Cfg, ∃ t : ℕ,
      base.state = (TrackedBankedCall.machine M).qStart ∧
      base.cells (TrackedBankedCall.machine M).outTape =
        (TrackedBankedCall.machine M).tapeOf
          ((TrackedBankedCall.machine M).blank ::
            (TrackedBankPreparation.inputWord M x y).map
              (fun s => some (s, true))) ∧
      base.head (TrackedBankedCall.machine M).outTape = 1 ∧
      (∀ i : Fin (M.k + 2), 2 ≤ i.val →
        base.cells i = (TrackedBankedCall.machine M).tapeOf [] ∧ base.head i = 1) ∧
      t ≤ T + 5 * TrackedBankCleanup.span M
        (TrackedBankedSimulation.extents M (M.initCfg x y)
          (TrackedBankPreparation.initialExtent M x y) T) +
        2 * (TrackedBankPreparation.inputWord M x y).length + 13 ∧
      (TrackedBankedCall.machine M).step^[t] base =
        TrackedBankedCall.finalFrame M base 1 (fun _ => 1)
          (TrackedBankedSimulation.extents M (M.initCfg x y)
            (TrackedBankPreparation.initialExtent M x y) T)
          (M.step^[T] (M.initCfg x y)) w := by sorry
