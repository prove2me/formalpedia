-- Prove2me | Theorems.Thm_BitcoinHeader_versionOutdated_iff
-- name    : BitcoinHeader.versionOutdated_iff
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T04:18:41.328386+00:00
-- url     : https://prove2.me/theorems/ef4a20a9-4647-4cf0-b37b-e29912aca902
-- title:
--   The outdated-version condition as height thresholds
-- statement:
--   For every version $v$ and previous height $p$, $\mathrm{versionOutdated}(v, p)$ holds exactly when
--   $$(v < 2 \wedge 227{,}931 \le p + 1) \;\vee\; (v < 3 \wedge 363{,}725 \le p + 1) \;\vee\; (v < 4 \wedge 388{,}381 \le p + 1),$$
--   the BIP34, BIP66 and BIP65 version floors at their mainnet activation heights.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: CBlockIndex::GetMedianTimePast and nMedianTimeSpan, MAX_FUTURE_BLOCK_TIME, src/chain.h: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/chain.h; ContextualCheckBlockHeader, src/validation.cpp (lines 4091-4128): https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; DeploymentActiveAfter (buried), src/deploymentstatus.h; BIP34Height, BIP66Height, BIP65Height in CMainParams, src/kernel/chainparams.cpp

import Definitions.Def_BitcoinHeader

theorem BitcoinHeader.versionOutdated_iff (version : Int) (prevHeight : Nat) :
    BitcoinHeader.versionOutdated version prevHeight = true ↔
      (version < 2 ∧ BitcoinHeader.BIP34Height ≤ prevHeight + 1) ∨
      (version < 3 ∧ BitcoinHeader.BIP66Height ≤ prevHeight + 1) ∨
      (version < 4 ∧ BitcoinHeader.BIP65Height ≤ prevHeight + 1) := by sorry
