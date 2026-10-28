-- Prove2me | Theorems.Thm_BitcoinPow_nextWork_off_boundary
-- name    : BitcoinPow.nextWork_off_boundary
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T04:29:17.215198+00:00
-- url     : https://prove2.me/theorems/37dfe526-8e53-455c-92a5-9621f73efbc6
-- title:
--   Off a retarget boundary the required word is unchanged and permitted
-- statement:
--   For every last height $h$ with $h + 1 \not\equiv 0 \pmod{2016}$, every last word $c$, and all block times,
--   $$\mathrm{nextWorkRequired}(h, c, t_{\text{last}}, t_{\text{first}}) = c \qquad\text{and}\qquad \mathrm{permittedTransition}(h+1, c, c) = \mathtt{true}.$$
--   On mainnet, where minimum-difficulty blocks are disabled, `GetNextWorkRequired` returns the previous word between retargets, and `PermittedDifficultyTransition` accepts an unchanged word there.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: GetNextWorkRequired (lines 14-48), CalculateNextWorkRequired (50-85), PermittedDifficultyTransition (89-136), DeriveTarget (146-159), CheckProofOfWorkImpl (161-171), src/pow.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/pow.cpp; arith_uint256::SetCompact (176-194), GetCompact (196-216), base_uint::operator<<= (15-30), operator*=(uint32_t) (49-59), operator/= (77-104), bits() (205-218), src/arith_uint256.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/arith_uint256.cpp; CMainParams powLimit, nPowTargetTimespan, nPowTargetSpacing, fPowAllowMinDifficultyBlocks, fPowNoRetargeting, enforce_BIP94, src/kernel/chainparams.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/kernel/chainparams.cpp

import Definitions.Def_BitcoinPow

theorem BitcoinPow.nextWork_off_boundary (lastHeight : Nat) (lastBits : BitVec 32) (lastTime firstTime : Int)
    (h : (lastHeight + 1) % BitcoinPow.difficultyAdjustmentInterval ≠ 0) :
    BitcoinPow.nextWorkRequired lastHeight lastBits lastTime firstTime = lastBits ∧
    BitcoinPow.permittedTransition (lastHeight + 1) lastBits lastBits = true := by sorry
