-- Prove2me | Theorems.Thm_BitcoinPow_nextWork_le_powLimit
-- name    : BitcoinPow.nextWork_le_powLimit
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T04:29:07.713606+00:00
-- url     : https://prove2.me/theorems/959570df-a350-4b1b-8f23-48ce29537c1c
-- title:
--   The next required target never exceeds the proof-of-work limit
-- statement:
--   For every last word $c$ and all block times $t_{\text{last}}, t_{\text{first}} \in \mathbb Z$,
--   $$\mathrm{setCompact}\big(\mathrm{calculateNextWork}(c, t_{\text{last}}, t_{\text{first}})\big) \le 2^{224} - 1.$$
--   The retarget caps its result at $\mathrm{powLimit}$ before re-encoding, and re-encoding rounds down, so the decoded next target is at most the limit. No hypothesis is placed on $c$.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: GetNextWorkRequired (lines 14-48), CalculateNextWorkRequired (50-85), PermittedDifficultyTransition (89-136), DeriveTarget (146-159), CheckProofOfWorkImpl (161-171), src/pow.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/pow.cpp; arith_uint256::SetCompact (176-194), GetCompact (196-216), base_uint::operator<<= (15-30), operator*=(uint32_t) (49-59), operator/= (77-104), bits() (205-218), src/arith_uint256.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/arith_uint256.cpp; CMainParams powLimit, nPowTargetTimespan, nPowTargetSpacing, fPowAllowMinDifficultyBlocks, fPowNoRetargeting, enforce_BIP94, src/kernel/chainparams.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/kernel/chainparams.cpp

import Definitions.Def_BitcoinPow

theorem BitcoinPow.nextWork_le_powLimit (lastBits : BitVec 32) (lastTime firstTime : Int) :
    BitcoinPow.setCompact (BitcoinPow.calculateNextWork lastBits lastTime firstTime) ≤ BitcoinPow.powLimit := by sorry
