-- Prove2me | Theorems.Thm_BitcoinPow_getCompact_le
-- name    : BitcoinPow.getCompact_le
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T04:28:30.624391+00:00
-- url     : https://prove2.me/theorems/40f74281-553f-4d3e-853a-f3551e2c2ca4
-- title:
--   Re-encoding a target rounds it down
-- statement:
--   For every $v < 2^{256}$,
--   $$\mathrm{setCompact}(\mathrm{getCompact}(v)) \le v.$$
--   `GetCompact` keeps only the top three bytes of $v$ (fewer when the mantissa's bit 23 forces a further byte shift), so decoding the result gives $v$ with some low bits cleared, never more than $v$. The case $v = 0$ is included and gives $0$.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: GetNextWorkRequired (lines 14-48), CalculateNextWorkRequired (50-85), PermittedDifficultyTransition (89-136), DeriveTarget (146-159), CheckProofOfWorkImpl (161-171), src/pow.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/pow.cpp; arith_uint256::SetCompact (176-194), GetCompact (196-216), base_uint::operator<<= (15-30), operator*=(uint32_t) (49-59), operator/= (77-104), bits() (205-218), src/arith_uint256.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/arith_uint256.cpp; CMainParams powLimit, nPowTargetTimespan, nPowTargetSpacing, fPowAllowMinDifficultyBlocks, fPowNoRetargeting, enforce_BIP94, src/kernel/chainparams.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/kernel/chainparams.cpp

import Definitions.Def_BitcoinPow

theorem BitcoinPow.getCompact_le (v : Nat) (hv : v < BitcoinPow.width) :
    BitcoinPow.setCompact (BitcoinPow.getCompact v) ≤ v := by sorry
