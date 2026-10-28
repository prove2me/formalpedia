-- Prove2me | Theorems.Thm_BitDFT_BankedTripleAlphabetHost_route_inverse_extra
-- name    : BitDFT.BankedTripleAlphabetHost.route_inverse_extra
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T15:19:41.236138+00:00
-- url     : https://prove2.me/theorems/e0bea058-9812-41dc-b8ca-13dc0afb4640
-- title:
--   Characterize physical tapes outside the multiplier bank
-- statement:
--   For the multiplier routing in the shared host, every non-input physical tape outside the multiplier’s own work bank is the image of an appended-bank tape.
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

theorem route_inverse_extra (A X H : MultitapeTM)
    (hoff : BitDFT.DedicatedTapeBanks.multiplierOffset A X H <
      4 + BitDFT.DedicatedTapeBanks.tail A X H)
    (p : Fin (BitDFT.DedicatedTapeBanks.width A X H))
    (hp : 1 ≤ p.val)
    (houtside : p.val < A.k ∨ A.k + X.k - 2 < p.val) :
    X.k ≤ ((route A X H
      (BitDFT.DedicatedTapeBanks.multiplierOffset A X H) hoff).symm p).val := by sorry
