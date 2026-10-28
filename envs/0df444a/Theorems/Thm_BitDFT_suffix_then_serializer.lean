-- Prove2me | Theorems.Thm_BitDFT_suffix_then_serializer
-- name    : BitDFT.suffix_then_serializer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T07:14:17.40881+00:00
-- url     : https://prove2.me/theorems/f8a072c9-86ec-4840-800a-674bc6f3e6f6
-- title:
--   Compose the multiplier suffix and routed serializer
-- statement:
--   Suppose a multiplier-side controller runs for a specified number of steps, does not reach its exit state early, and ends at that exit. If its lifted endpoint frame is the serializer's specified start frame, then the composed controller runs the multiplier segment, one stationary handoff, and the serializer segment, ending at the serializer's exact endpoint.
-- source:
--   The theorem lifts the multiplier run to the serializer's enlarged host using the exact configuration simulation, performs the one-step sequence handoff, then lifts the serializer run to the composed controller. The frame equality and no-early-exit condition state precisely the two interface facts needed for this composition.

import Definitions.Def_BitDFT_SerializerControllerBridge
set_option autoImplicit false
open IntMul BitDFT.MachineSequence BitDFT.RoutedCountedBlockFreshTapes

theorem BitDFT.suffix_then_serializer (M : MultitapeTM)
    (C : Controller (source M))
    (extraCells : Fin (extension M).k → ℕ → (source M).Sym)
    (extraHeads : Fin (extension M).k → ℕ)
    (c cEnd : C.machine.Cfg) (ts tr : ℕ)
    (hRun : C.machine.step^[ts] c = cEnd)
    (hNoEarlyExit : ∀ s, s < ts →
      ((suffixControllerOnSerializerHost M C).machine.step^[s]
        (suffixEmbed M C extraCells extraHeads c)).state ≠ C.exit)
    (hExit : cEnd.state = C.exit)
    (serStart serEnd : (serializerController M).machine.Cfg)
    (hFrame : BitDFT.MachineSequence.handoff (suffixControllerOnSerializerHost M C)
      (serializerController M) (suffixEmbed M C extraCells extraHeads cEnd) = serStart)
    (hSer : (serializerController M).machine.step^[tr] serStart = serEnd) :
    (suffixSerializerController M C).machine.step^[ts+1+tr]
      (BitDFT.MachineSequence.leftCfg (suffixControllerOnSerializerHost M C)
        (serializerController M) (suffixEmbed M C extraCells extraHeads c)) =
      BitDFT.MachineSequence.rightCfg (suffixControllerOnSerializerHost M C)
        (serializerController M) serEnd := by sorry
