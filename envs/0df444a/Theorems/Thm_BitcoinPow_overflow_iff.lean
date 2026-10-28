-- Prove2me | Theorems.Thm_BitcoinPow_overflow_iff
-- name    : BitcoinPow.overflow_iff
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T04:28:00.468669+00:00
-- url     : https://prove2.me/theorems/dc55ed00-c187-4dd8-b7ec-cf3f7ba1a08c
-- title:
--   The compact overflow flag is exactly the 256-bit bound
-- statement:
--   For every 32-bit word $c$ with size $S$ and mantissa $W$,
--   $$\mathrm{compactOverflow}(c) = \mathtt{true} \iff 2^{256} \le \mathrm{specTarget}(c),$$
--   where $\mathrm{specTarget}(c) = W \cdot 256^{S-3}$ for $S > 3$ and $\lfloor W / 256^{3-S} \rfloor$ otherwise. The flag computed by `SetCompact` from the three threshold tests on $S$ and $W$ is therefore not an approximation: it is set precisely when the encoded value does not fit in 256 bits. Both directions are asserted, for all $2^{32}$ words.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: GetNextWorkRequired (lines 14-48), CalculateNextWorkRequired (50-85), PermittedDifficultyTransition (89-136), DeriveTarget (146-159), CheckProofOfWorkImpl (161-171), src/pow.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/pow.cpp; arith_uint256::SetCompact (176-194), GetCompact (196-216), base_uint::operator<<= (15-30), operator*=(uint32_t) (49-59), operator/= (77-104), bits() (205-218), src/arith_uint256.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/arith_uint256.cpp; CMainParams powLimit, nPowTargetTimespan, nPowTargetSpacing, fPowAllowMinDifficultyBlocks, fPowNoRetargeting, enforce_BIP94, src/kernel/chainparams.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/kernel/chainparams.cpp

import Definitions.Def_BitcoinPow

theorem BitcoinPow.overflow_iff (c : BitVec 32) :
    BitcoinPow.compactOverflow c = true ↔ BitcoinPow.width ≤ BitcoinPow.specTarget c := by sorry
