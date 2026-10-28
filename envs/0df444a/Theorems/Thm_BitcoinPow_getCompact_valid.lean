-- Prove2me | Theorems.Thm_BitcoinPow_getCompact_valid
-- name    : BitcoinPow.getCompact_valid
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T04:28:40.759262+00:00
-- url     : https://prove2.me/theorems/32471b10-a36b-416f-a370-2c0b9251a761
-- title:
--   GetCompact never produces a negative or overflowing word
-- statement:
--   For every $v < 2^{256}$, the word $\mathrm{getCompact}(v)$ has its negative flag clear and its overflow flag clear. The mantissa it assembles is below $2^{23}$ after the bit-23 normalization, so the sign bit is never set, and its size byte is at most $33$ with a mantissa below $2^{16}$ in that extreme case, so none of the overflow thresholds is met.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: GetNextWorkRequired (lines 14-48), CalculateNextWorkRequired (50-85), PermittedDifficultyTransition (89-136), DeriveTarget (146-159), CheckProofOfWorkImpl (161-171), src/pow.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/pow.cpp; arith_uint256::SetCompact (176-194), GetCompact (196-216), base_uint::operator<<= (15-30), operator*=(uint32_t) (49-59), operator/= (77-104), bits() (205-218), src/arith_uint256.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/arith_uint256.cpp; CMainParams powLimit, nPowTargetTimespan, nPowTargetSpacing, fPowAllowMinDifficultyBlocks, fPowNoRetargeting, enforce_BIP94, src/kernel/chainparams.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/kernel/chainparams.cpp

import Definitions.Def_BitcoinPow

theorem BitcoinPow.getCompact_valid (v : Nat) (hv : v < BitcoinPow.width) :
    BitcoinPow.compactNegative (BitcoinPow.getCompact v) = false ∧
    BitcoinPow.compactOverflow (BitcoinPow.getCompact v) = false := by sorry
