-- Prove2me | Theorems.Thm_BitcoinPow_setCompact_eq_spec
-- name    : BitcoinPow.setCompact_eq_spec
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T04:28:10.800413+00:00
-- url     : https://prove2.me/theorems/84e7fc8e-b3ed-4b8d-8e0a-dccd343a97ce
-- title:
--   Without overflow, SetCompact decodes the exact value
-- statement:
--   For every 32-bit word $c$ whose overflow flag is clear,
--   $$\mathrm{setCompact}(c) = \mathrm{specTarget}(c).$$
--   The 256-bit register arithmetic of `SetCompact` (a left shift that drops carried-out bits) loses nothing when the flag is clear, so the decoded target is the mathematical value $W \cdot 256^{S-3}$ (or $\lfloor W / 256^{3-S} \rfloor$ for $S \le 3$).
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: GetNextWorkRequired (lines 14-48), CalculateNextWorkRequired (50-85), PermittedDifficultyTransition (89-136), DeriveTarget (146-159), CheckProofOfWorkImpl (161-171), src/pow.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/pow.cpp; arith_uint256::SetCompact (176-194), GetCompact (196-216), base_uint::operator<<= (15-30), operator*=(uint32_t) (49-59), operator/= (77-104), bits() (205-218), src/arith_uint256.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/arith_uint256.cpp; CMainParams powLimit, nPowTargetTimespan, nPowTargetSpacing, fPowAllowMinDifficultyBlocks, fPowNoRetargeting, enforce_BIP94, src/kernel/chainparams.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/kernel/chainparams.cpp

import Definitions.Def_BitcoinPow

theorem BitcoinPow.setCompact_eq_spec (c : BitVec 32) (h : BitcoinPow.compactOverflow c = false) :
    BitcoinPow.setCompact c = BitcoinPow.specTarget c := by sorry
