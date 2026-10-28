-- Prove2me | Theorems.Thm_BitDFT_BankedTripleAlphabetHost_config_extra_tape
-- name    : BitDFT.BankedTripleAlphabetHost.config_extra_tape
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T15:19:45.072985+00:00
-- url     : https://prove2.me/theorems/e3ca2473-0644-4b1d-9417-f8ec19b815dc
-- title:
--   Preserve an appended caller tape during component execution
-- statement:
--   Any host tape routed from the appended region beyond a component’s own tapes retains exactly the caller-supplied tape contents and head in the embedded configuration.
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

theorem config_extra_tape (A M H X : MultitapeTM)
    (e : AlphabetEmbedding.Map X (carrier A M H))
    (offset : ℕ) (hoff : offset < 4 + BitDFT.DedicatedTapeBanks.tail A M H)
    (hX : X.k ≤ BitDFT.DedicatedTapeBanks.width A M H)
    (extraCells : Fin (BitDFT.DedicatedTapeBanks.width A M H) → ℕ → (carrier A M H).Sym)
    (extraHeads : Fin (BitDFT.DedicatedTapeBanks.width A M H) → ℕ)
    (c : X.Cfg) (j : Fin (BitDFT.DedicatedTapeBanks.width A M H))
    (hj : X.k ≤ j.val) :
    (config A M H X e offset hoff hX extraCells extraHeads c).cells
      (route A M H offset hoff j) = extraCells (route A M H offset hoff j) ∧
    (config A M H X e offset hoff hX extraCells extraHeads c).head
      (route A M H offset hoff j) = extraHeads (route A M H offset hoff j) := by sorry
