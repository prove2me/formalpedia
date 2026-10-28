-- Prove2me | Theorems.Thm_BitcoinHeader_mtp_mem
-- name    : BitcoinHeader.mtp_mem
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T04:17:58.158883+00:00
-- url     : https://prove2.me/theorems/030fa8b4-33df-4eaf-bfef-ee4c9022ad32
-- title:
--   The median time past is one of the chain's times
-- statement:
--   For every non-empty chain of times, $\mathrm{MTP}(\text{times}) \in \text{times}$. Immediate from window membership, since the window is a prefix of the chain.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: CBlockIndex::GetMedianTimePast and nMedianTimeSpan, MAX_FUTURE_BLOCK_TIME, src/chain.h: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/chain.h; ContextualCheckBlockHeader, src/validation.cpp (lines 4091-4128): https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; DeploymentActiveAfter (buried), src/deploymentstatus.h; BIP34Height, BIP66Height, BIP65Height in CMainParams, src/kernel/chainparams.cpp

import Definitions.Def_BitcoinHeader

theorem BitcoinHeader.mtp_mem (times : List Int) (h : times ≠ []) :
    BitcoinHeader.medianTimePast times ∈ times := by sorry
