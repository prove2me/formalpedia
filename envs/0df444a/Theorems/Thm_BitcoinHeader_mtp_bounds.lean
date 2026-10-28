-- Prove2me | Theorems.Thm_BitcoinHeader_mtp_bounds
-- name    : BitcoinHeader.mtp_bounds
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T04:18:08.342747+00:00
-- url     : https://prove2.me/theorems/bf3d4a4a-3cb5-499f-aeb7-3e21f0a48233
-- title:
--   The median time past lies within any bounds of the window
-- statement:
--   For every non-empty chain and integers $lo \le hi$ such that every time $t$ in the window satisfies $lo \le t \le hi$, also $lo \le \mathrm{MTP}(\text{times}) \le hi$. In particular the median is between the oldest and the newest time of the window.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: CBlockIndex::GetMedianTimePast and nMedianTimeSpan, MAX_FUTURE_BLOCK_TIME, src/chain.h: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/chain.h; ContextualCheckBlockHeader, src/validation.cpp (lines 4091-4128): https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; DeploymentActiveAfter (buried), src/deploymentstatus.h; BIP34Height, BIP66Height, BIP65Height in CMainParams, src/kernel/chainparams.cpp

import Definitions.Def_BitcoinHeader

theorem BitcoinHeader.mtp_bounds (times : List Int) (h : times ≠ []) (lo hi : Int)
    (hb : ∀ t ∈ BitcoinHeader.timeWindow times, lo ≤ t ∧ t ≤ hi) :
    lo ≤ BitcoinHeader.medianTimePast times ∧ BitcoinHeader.medianTimePast times ≤ hi := by sorry
