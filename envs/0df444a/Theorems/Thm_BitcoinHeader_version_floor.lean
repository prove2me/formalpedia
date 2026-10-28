-- Prove2me | Theorems.Thm_BitcoinHeader_version_floor
-- name    : BitcoinHeader.version_floor
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T04:18:57.88671+00:00
-- url     : https://prove2.me/theorems/f277b663-b1d2-49f2-9a65-a4d8faebd1f0
-- title:
--   Accepted headers respect the version floors after activation
-- statement:
--   For every header accepted by the contextual check against previous height $p$: if $227{,}931 \le p + 1$ then its version is at least 2; if $363{,}725 \le p + 1$ then at least 3; if $388{,}381 \le p + 1$ then at least 4.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: CBlockIndex::GetMedianTimePast and nMedianTimeSpan, MAX_FUTURE_BLOCK_TIME, src/chain.h: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/chain.h; ContextualCheckBlockHeader, src/validation.cpp (lines 4091-4128): https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; DeploymentActiveAfter (buried), src/deploymentstatus.h; BIP34Height, BIP66Height, BIP65Height in CMainParams, src/kernel/chainparams.cpp

import Definitions.Def_BitcoinHeader

theorem BitcoinHeader.version_floor (h : BitcoinHeader.Header) (prevHeight : Nat) (prevTimes : List Int)
    (required : BitVec 32) (now : Int)
    (hc : BitcoinHeader.contextualCheck h prevHeight prevTimes required now = true) :
    (BitcoinHeader.BIP34Height ≤ prevHeight + 1 → 2 ≤ h.version) ∧
    (BitcoinHeader.BIP66Height ≤ prevHeight + 1 → 3 ≤ h.version) ∧
    (BitcoinHeader.BIP65Height ≤ prevHeight + 1 → 4 ≤ h.version) := by sorry
