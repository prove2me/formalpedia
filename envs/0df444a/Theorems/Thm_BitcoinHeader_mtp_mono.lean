-- Prove2me | Theorems.Thm_BitcoinHeader_mtp_mono
-- name    : BitcoinHeader.mtp_mono
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T04:18:29.198836+00:00
-- url     : https://prove2.me/theorems/068eaf7e-b929-49ba-8f85-ef2698acc7a9
-- title:
--   Appending a block that passes time-too-old never lowers the median
-- statement:
--   For every chain of times $c$ and time $t$ with $\mathrm{MTP}(c) < t$,
--   $$\mathrm{MTP}(c) \le \mathrm{MTP}(t :: c).$$
--   The new window is $t$ followed by the ten most recent times of $c$: it gains $t$, which lies above the old median, and loses at most the eleventh time of the old window. For a chain shorter than eleven blocks the window grows instead and the median index may move; the inequality holds in both cases.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: CBlockIndex::GetMedianTimePast and nMedianTimeSpan, MAX_FUTURE_BLOCK_TIME, src/chain.h: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/chain.h; ContextualCheckBlockHeader, src/validation.cpp (lines 4091-4128): https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; DeploymentActiveAfter (buried), src/deploymentstatus.h; BIP34Height, BIP66Height, BIP65Height in CMainParams, src/kernel/chainparams.cpp

import Definitions.Def_BitcoinHeader

theorem BitcoinHeader.mtp_mono (times : List Int) (t : Int)
    (h : BitcoinHeader.medianTimePast times < t) :
    BitcoinHeader.medianTimePast times ≤ BitcoinHeader.medianTimePast (t :: times) := by sorry
