-- Prove2me | Theorems.Thm_BitcoinPow_round_mono
-- name    : BitcoinPow.round_mono
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T04:28:50.010415+00:00
-- url     : https://prove2.me/theorems/7bdaa9ab-7904-4d75-853d-fabfabb042fc
-- title:
--   Compact rounding is order-preserving
-- statement:
--   For all $v \le w$ with $w < 2^{256}$,
--   $$\mathrm{setCompact}(\mathrm{getCompact}(v)) \le \mathrm{setCompact}(\mathrm{getCompact}(w)).$$
--   Decoding after encoding clears a number of low bits that depends only on the position of the top bit; values with the same top bit are rounded on the same grid, and a value with a lower top bit is below the retained top bit of the other. This is the property `PermittedDifficultyTransition` relies on when it compares re-encoded bounds with a decoded word.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: GetNextWorkRequired (lines 14-48), CalculateNextWorkRequired (50-85), PermittedDifficultyTransition (89-136), DeriveTarget (146-159), CheckProofOfWorkImpl (161-171), src/pow.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/pow.cpp; arith_uint256::SetCompact (176-194), GetCompact (196-216), base_uint::operator<<= (15-30), operator*=(uint32_t) (49-59), operator/= (77-104), bits() (205-218), src/arith_uint256.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/arith_uint256.cpp; CMainParams powLimit, nPowTargetTimespan, nPowTargetSpacing, fPowAllowMinDifficultyBlocks, fPowNoRetargeting, enforce_BIP94, src/kernel/chainparams.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/kernel/chainparams.cpp

import Definitions.Def_BitcoinPow

theorem BitcoinPow.round_mono (v w : Nat) (hvw : v ≤ w) (hw : w < BitcoinPow.width) :
    BitcoinPow.setCompact (BitcoinPow.getCompact v) ≤ BitcoinPow.setCompact (BitcoinPow.getCompact w) := by sorry
