-- Prove2me | Theorems.Thm_BitDFT_BankedTripleAlphabetHost_run
-- name    : BitDFT.BankedTripleAlphabetHost.run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T15:19:20.471292+00:00
-- url     : https://prove2.me/theorems/4d9ddeba-d1a1-48bb-9e8d-80411fcc7f4c
-- title:
--   Run a component in its routed tape bank at the exact clock
-- statement:
--   In a shared host with a common symbol alphabet and disjoint tape banks, running any component for t steps updates exactly its routed tapes as that component would. All parked host tapes retain their supplied contents and heads, and the host run takes exactly t transitions.
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

theorem run (A M H X : MultitapeTM) (e : AlphabetEmbedding.Map X (carrier A M H))
    (offset : ℕ) (hoff : offset < 4 + BitDFT.DedicatedTapeBanks.tail A M H)
    (hX : X.k ≤ BitDFT.DedicatedTapeBanks.width A M H)
    (extraCells : Fin (BitDFT.DedicatedTapeBanks.width A M H) → ℕ → (carrier A M H).Sym)
    (extraHeads : Fin (BitDFT.DedicatedTapeBanks.width A M H) → ℕ) (c : X.Cfg) (t : ℕ) :
    (machine A M H X e offset hoff hX).step^[t]
      (config A M H X e offset hoff hX extraCells extraHeads c) =
    config A M H X e offset hoff hX extraCells extraHeads (X.step^[t] c) := by sorry
