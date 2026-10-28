-- Prove2me | Theorems.Thm_BitDFT_scaled_product_placed_block
-- name    : BitDFT.scaled_product_placed_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T23:13:51.541077+00:00
-- url     : https://prove2.me/theorems/4ed1cbd9-569b-43f2-a0de-b2e36a0b4b5e
-- title:
--   Run the scaled-product serializer in the routed output layout
-- statement:
--   Assume a product magnitude word is arranged on the serializer's source tape after a leading-zero prefix, and the sign bit is already at the end of the output prefix. If a descriptor requests exactly the remaining product width, then the counted-block magnitude-copy phase executes inside the signed-block host's routed tape layout. The run preserves the parked host tapes and halts in the expected output frame, with cost at most 6 times the requested width plus four times the descriptor length plus two.
-- source:
--   Actual tape-layout composition for one scaled-product serialization step, reusing the accepted counted-block run, signed-block sequence, work relocation, alphabet embedding, tape extension, and tape permutation invariants.

import Definitions.Def_BitDFT_SignedBlockPlacement
import Theorems.Thm_BitDFT_counted_block_correct
import Theorems.Thm_BitDFT_signed_block_correct
import Theorems.Thm_BitDFT_work_relocation_correct
import Theorems.Thm_BitDFT_machine_sequence_bound
import Theorems.Thm_BitDFT_alphabet_embedding_correct
import Theorems.Thm_BitDFT_tape_extension_correct
import Theorems.Thm_BitDFT_tape_permutation_run
set_option autoImplicit false
open IntMul BitDFT.MachineSequence

theorem BitDFT.scaled_product_placed_block (N : MultitapeTM) (k : ℕ)
    (cells : Fin (5+(k+3)) → ℕ → N.Sym) (heads : Fin (5+(k+3)) → ℕ)
    (rootCells : ℕ → TapeCopy.Sym) (rootHead : ℕ)
    (pre out : List Bool) (sign : Bool) (x descriptor : List Bool)
    (hx : val descriptor + 1 ≤ x.length) :
    ∃ t : ℕ, t ≤ 6*(val descriptor+1)+4*descriptor.length+2 ∧
      (BitDFT.SignedBlockPlacement.machine N k).step^[t]
        (BitDFT.SignedBlockPlacement.embed N k cells heads
          (BitDFT.WorkRelocation.embed BitDFT.SignedBlock.machine rootCells rootHead
            (BitDFT.MachineSequence.rightCfg BitDFT.SignedBlock.signControl
              BitDFT.SignedBlock.blockControl
              (BitDFT.SignedBlock.blockFrame
                (BitDFT.CountedBlock.frame pre (out++[sign]) x descriptor
                  descriptor.reverse 0 .emit))))) =
      BitDFT.SignedBlockPlacement.embed N k cells heads
        (BitDFT.WorkRelocation.embed BitDFT.SignedBlock.machine rootCells rootHead
          (BitDFT.MachineSequence.rightCfg BitDFT.SignedBlock.signControl
            BitDFT.SignedBlock.blockControl
            (BitDFT.SignedBlock.blockFrame
              (BitDFT.CountedBlock.frame pre (out++[sign]) x descriptor
                descriptor.reverse (val descriptor+1) .halt)))) := by sorry
