-- Prove2me | Theorems.Thm_BitcoinHeader_mtp_take
-- name    : BitcoinHeader.mtp_take
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T04:18:19.096164+00:00
-- url     : https://prove2.me/theorems/868727d5-2c4f-4b7f-bed6-51a15e0bf90c
-- title:
--   Only the eleven most recent times determine the median
-- statement:
--   For every chain of times, $\mathrm{MTP}(\text{times}) = \mathrm{MTP}(\text{first eleven of times})$: block times older than the eleventh ancestor have no influence on the median time past.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: CBlockIndex::GetMedianTimePast and nMedianTimeSpan, MAX_FUTURE_BLOCK_TIME, src/chain.h: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/chain.h; ContextualCheckBlockHeader, src/validation.cpp (lines 4091-4128): https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; DeploymentActiveAfter (buried), src/deploymentstatus.h; BIP34Height, BIP66Height, BIP65Height in CMainParams, src/kernel/chainparams.cpp

import Definitions.Def_BitcoinHeader

theorem BitcoinHeader.mtp_take (times : List Int) :
    BitcoinHeader.medianTimePast times = BitcoinHeader.medianTimePast (times.take BitcoinHeader.nMedianTimeSpan) := by sorry
