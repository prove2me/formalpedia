-- Prove2me | Theorems.Thm_BitcoinHeader_mtp_mem_window
-- name    : BitcoinHeader.mtp_mem_window
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T04:17:46.624824+00:00
-- url     : https://prove2.me/theorems/b9ddad4f-a894-45ee-8853-d84192c213be
-- title:
--   The median time past is one of the window's times
-- statement:
--   For every non-empty chain of times, $\mathrm{MTP}(\text{times}) \in \mathrm{timeWindow}(\text{times})$: the median is an element of the (at most eleven) most recent block times, not an average or an interpolation.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: CBlockIndex::GetMedianTimePast and nMedianTimeSpan, MAX_FUTURE_BLOCK_TIME, src/chain.h: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/chain.h; ContextualCheckBlockHeader, src/validation.cpp (lines 4091-4128): https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; DeploymentActiveAfter (buried), src/deploymentstatus.h; BIP34Height, BIP66Height, BIP65Height in CMainParams, src/kernel/chainparams.cpp

import Definitions.Def_BitcoinHeader

theorem BitcoinHeader.mtp_mem_window (times : List Int) (h : times ≠ []) :
    BitcoinHeader.medianTimePast times ∈ BitcoinHeader.timeWindow times := by sorry
