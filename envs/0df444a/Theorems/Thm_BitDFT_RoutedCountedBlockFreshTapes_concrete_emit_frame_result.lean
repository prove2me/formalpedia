-- Prove2me | Theorems.Thm_BitDFT_RoutedCountedBlockFreshTapes_concrete_emit_frame_result
-- name    : BitDFT.RoutedCountedBlockFreshTapes.concrete_emit_frame_result
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T08:17:16.050725+00:00
-- url     : https://prove2.me/theorems/f8f33c14-2ce7-4f41-bb63-2fd1af5ff84d
-- title:
--   The product frame matches the routed serializer emit frame
-- statement:
--   Let a multiplier controller finish in configuration cEnd, and suppose its product tape contains the encoded bit string pre ++ x with its head at the first bit of x. The product, preserved old tapes, and serializer work tapes can be arranged so that handing off to the emit-phase serializer yields exactly the routed counted-block emit configuration.
-- source:
--   This is the concrete endpoint-frame equality needed to compose a multiplier suffix with the already-proved counted-block serializer run. The product tape is transferred through the alphabet embedding, while the routing sends each old multiplier tape back to its preserved extension slot and places the output, countdown, and template on the appended tapes.

import Definitions.Def_BitDFT_ConcreteEmitFrame
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
open IntMul BitDFT.MachineSequence BitDFT.RoutedCountedBlockFreshTapes

theorem BitDFT.RoutedCountedBlockFreshTapes.concrete_emit_frame_result (M : MultitapeTM) (C : Controller (source M))
    (cEnd : C.machine.Cfg) (pre out x y : List Bool)
    (hProductCells : cEnd.cells ⟨1, by dsimp [source, IntMul.TrackedOutputShift.machine]; omega⟩ =
      (host M).tapeOf ((pre ++ x).map (host M).bitSym))
    (hProductHead : cEnd.head ⟨1, by dsimp [source, IntMul.TrackedOutputShift.machine]; omega⟩ =
      pre.length + 1) :
    MachineSequence.handoff (suffixControllerOnSerializerHost M C)
      (serializerEmitContinuation M)
      (suffixEmbed M C
        (fun j p => if j.val < (source M).k then (source M).blank else
          (emitFrame M
            ⟨(host M).qStart,
              (fun i p => if i.val = 0 then cEnd.cells ⟨0, by
                dsimp [source, IntMul.TrackedOutputShift.machine]; omega⟩ p else (host M).blank),
              (fun i => if i.val = 0 then cEnd.head ⟨0, by
                dsimp [source, IntMul.TrackedOutputShift.machine]; omega⟩ else 0)⟩
            (parkedCells M cEnd.cells) (parkedHeads M cEnd.head) pre out x y).cells j p)
        (fun j => if j.val < (source M).k then 0 else
          (emitFrame M
            ⟨(host M).qStart,
              (fun i p => if i.val = 0 then cEnd.cells ⟨0, by
                dsimp [source, IntMul.TrackedOutputShift.machine]; omega⟩ p else (host M).blank),
              (fun i => if i.val = 0 then cEnd.head ⟨0, by
                dsimp [source, IntMul.TrackedOutputShift.machine]; omega⟩ else 0)⟩
            (parkedCells M cEnd.cells) (parkedHeads M cEnd.head) pre out x y).head j)
        cEnd) =
    ⟨CountedStream.State.emit,
        (emitFrame M
          ⟨(host M).qStart,
            (fun i p => if i.val = 0 then cEnd.cells ⟨0, by
              dsimp [source, IntMul.TrackedOutputShift.machine]; omega⟩ p else (host M).blank),
            (fun i => if i.val = 0 then cEnd.head ⟨0, by
              dsimp [source, IntMul.TrackedOutputShift.machine]; omega⟩ else 0)⟩
          (parkedCells M cEnd.cells) (parkedHeads M cEnd.head) pre out x y).cells,
        (emitFrame M
          ⟨(host M).qStart,
            (fun i p => if i.val = 0 then cEnd.cells ⟨0, by
              dsimp [source, IntMul.TrackedOutputShift.machine]; omega⟩ p else (host M).blank),
            (fun i => if i.val = 0 then cEnd.head ⟨0, by
              dsimp [source, IntMul.TrackedOutputShift.machine]; omega⟩ else 0)⟩
          (parkedCells M cEnd.cells) (parkedHeads M cEnd.head) pre out x y).head⟩ := by sorry
