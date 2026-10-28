-- Prove2me | Theorems.Thm_BitDFT_BankedTripleAlphabetHost_config_component_tape
-- name    : BitDFT.BankedTripleAlphabetHost.config_component_tape
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T15:19:27.412181+00:00
-- url     : https://prove2.me/theorems/8603bd9c-cc84-4984-83a0-c20cffc1d257
-- title:
--   Project a routed component tape to its exact host contents
-- statement:
--   For any component tape in the shared host, its routed host address contains the component tape with every symbol encoded by the common alphabet map, and its head position is unchanged.
-- source:
--   Exact tape-bank routing proof for the finite-precision Fourier output-scaling construction. This theorem is an interface component and does not claim to assemble the full rescaling or DFT machine.

import Definitions.Def_BitDFT_BankedTripleAlphabetHost
import Definitions.Def_BitDFT_BankedOperandStage
import Theorems.Thm_BitDFT_alphabet_embedding_correct
import Theorems.Thm_BitDFT_tape_extension_correct
import Theorems.Thm_BitDFT_tape_count_transport_correct
import Theorems.Thm_BitDFT_tape_permutation_run
set_option autoImplicit false
noncomputable section
namespace BitDFT.BankedTripleAlphabetHost
open IntMul BitDFT.AlphabetEmbedding

theorem config_component_tape (A M H X : MultitapeTM)
    (e : AlphabetEmbedding.Map X (carrier A M H))
    (offset : ℕ) (hoff : offset < 4 + BitDFT.DedicatedTapeBanks.tail A M H)
    (hX : X.k ≤ BitDFT.DedicatedTapeBanks.width A M H)
    (extraCells : Fin (BitDFT.DedicatedTapeBanks.width A M H) → ℕ → (carrier A M H).Sym)
    (extraHeads : Fin (BitDFT.DedicatedTapeBanks.width A M H) → ℕ)
    (c : X.Cfg) (j : Fin X.k) :
    let h : X.k + (BitDFT.DedicatedTapeBanks.width A M H - X.k) =
        BitDFT.DedicatedTapeBanks.width A M H := Nat.add_sub_of_le hX
    let logical := Fin.cast h (TapeExtension.oldTape X
      (BitDFT.DedicatedTapeBanks.width A M H - X.k) j)
    (config A M H X e offset hoff hX extraCells extraHeads c).cells
      (route A M H offset hoff logical) = (fun p => e.encode (c.cells j p)) ∧
    (config A M H X e offset hoff hX extraCells extraHeads c).head
      (route A M H offset hoff logical) = c.head j := by sorry
