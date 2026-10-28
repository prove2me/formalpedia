-- Prove2me | Theorems.Thm_BitcoinBIP68_height_vector
-- name    : BitcoinBIP68.height_vector
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T01:35:41.743684+00:00
-- url     : https://prove2.me/theorems/d46f95e7-6eee-4dc7-83dd-787ad3545c04
-- title:
--   Sequence-lock calculation preserves exactly the relevant heights
-- statement:
--   For any unsigned 32-bit version and flags, any context, and any finite input list $I=[(s_i,c_i)]$, let $E$ mean that version is at least two and flags bit zero is set. After calculation, the returned height list has the original length and order and satisfies
--
--   $$h_i'=\begin{cases}0,&E\text{ and sequence bit 31 is set},\\c_i,&\text{otherwise}.\end{cases}$$
--
--   This is equality of ordered lists, including repeated entries. If enforcement is off, every input height is unchanged even when its sequence-disable bit is set. The theorem imposes no admissibility or no-overflow assumption on the mathematical model and includes the empty list. It records the height-vector side effect separately from acceptance.
-- source:
--   BIP68, Specification and Implementation: https://github.com/bitcoin/bips/blob/100ba872c808946155b1eeb8c4568058f2eea0a7/bip-0068.mediawiki; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48, CalculateSequenceLocks (lines 45–101), EvaluateSequenceLocks (103–111), SequenceLocks (113–116): https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/tx_verify.cpp#L45-L116. Functional contract extracted from these routines; the BIP does not number these claims as mathematical theorems.

import Definitions.Def_BIP68_Model
import Definitions.Def_BIP68_Core

theorem BitcoinBIP68.height_vector (version flags : BitVec 32)
    (ctx : BitcoinBIP68.Context) (inputs : List BitcoinBIP68.Input) :
    BitcoinBIP68.returnedHeights (BitcoinBIP68.calculate version flags ctx inputs) =
      BitcoinBIP68.expectedHeights version flags inputs := by sorry
