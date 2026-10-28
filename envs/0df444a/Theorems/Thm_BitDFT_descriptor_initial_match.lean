-- Prove2me | Theorems.Thm_BitDFT_descriptor_initial_match
-- name    : BitDFT.descriptor_initial_match
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T18:22:07.202758+00:00
-- url     : https://prove2.me/theorems/132fbd3f-dcdc-4557-8d95-4fbd2cda4e65
-- title:
--   Concrete physical tape conditions reconstruct the routed setup initial configuration
-- statement:
--   Consider a configuration of the routed descriptor machine in its starting state. Suppose its native input matches the supplied parked base, tape k+3 contains y with its head immediately after the word, and tapes k+5 and k+6 are blank with heads at their markers. Then the complete configuration equals the embedding of the descriptor routine initial configuration, with every other tape taken from the given configuration. This establishes the interface needed to invoke the existing runtime theorem without assuming any free tape initialization.
-- source:
--   Configuration bridge for saved precision and fresh descriptor tapes in the exact DFT output scaler.

import Definitions.Def_BitDFT_DescriptorPlacement
open BitDFT.DescriptorPlacement BitDFT IntMul

theorem BitDFT.descriptor_initial_match (N : MultitapeTM) (k : ℕ) (hk : 2 ≤ k)
    (d : (machine N k).Cfg) (base : RewoundDescriptor.storage.Cfg) (y : List Bool)
    (hs : d.state = (machine N k).qStart)
    (hroot : d.cells ⟨0,by change 0 < 4+(k+3); omega⟩ = (fun p => PreprocessorAlphabet.encode N (base.cells 0 p)))
    (hrootHead : d.head ⟨0,by change 0 < 4+(k+3); omega⟩ = base.head 0)
    (hp : d.cells (precisionTape k) = N.tapeOf (y.map N.bitSym))
    (hpHead : d.head (precisionTape k) = y.length+1)
    (hc : d.cells (counterTape k) = N.tapeOf []) (hcHead : d.head (counterTape k) = 0)
    (ht : d.cells (templateTape k) = N.tapeOf []) (htHead : d.head (templateTape k) = 0) :
    embed N k d.cells d.head (RewoundDescriptor.initial base y) = d := by sorry
