-- Prove2me | Theorems.Thm_BitcoinPow_nextWork_permitted
-- name    : BitcoinPow.nextWork_permitted
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T04:29:27.041891+00:00
-- url     : https://prove2.me/theorems/f1c9f809-eb67-4a7c-b646-7b9e7ddf14c5
-- title:
--   The retarget always passes the permitted-transition check
-- statement:
--   For every height $h$ divisible by $2016$, every last word $c_{\text{old}}$ whose decoded value is at most $\mathrm{powLimit} = 2^{224} - 1$, and all block times $t_{\text{last}}, t_{\text{first}} \in \mathbb Z$,
--   $$\mathrm{permittedTransition}\big(h,\ c_{\text{old}},\ \mathrm{calculateNextWork}(c_{\text{old}}, t_{\text{last}}, t_{\text{first}})\big) = \mathtt{true}.$$
--   Here `calculateNextWork` is the mainnet `CalculateNextWorkRequired`: decode, multiply by the clamped elapsed time inside 256 bits, divide by $T$, cap, re-encode. `permittedTransition` is the mainnet `PermittedDifficultyTransition`: the decoded new word must lie between the re-encoded caps of $c_{\text{old}} \cdot (T/4) / T$ and $c_{\text{old}} \cdot 4T / T$.
--
--   The hypothesis on $c_{\text{old}}$ holds for every word `DeriveTarget` accepts, hence for every block on a valid chain; under it none of the three 256-bit products wraps. The statement is the consistency of the two functions: a header carrying the required `nBits` is never rejected by the cheap header-chain check, whatever the timestamps.
--
--   **Formalization Note.** The proof reduces to the monotonicity of the rounding map $\mathrm{setCompact} \circ \mathrm{getCompact}$ and to the ordering of the three capped quotients; no assumption that $c_{\text{old}}$ is itself a `GetCompact` output is made.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: GetNextWorkRequired (lines 14-48), CalculateNextWorkRequired (50-85), PermittedDifficultyTransition (89-136), DeriveTarget (146-159), CheckProofOfWorkImpl (161-171), src/pow.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/pow.cpp; arith_uint256::SetCompact (176-194), GetCompact (196-216), base_uint::operator<<= (15-30), operator*=(uint32_t) (49-59), operator/= (77-104), bits() (205-218), src/arith_uint256.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/arith_uint256.cpp; CMainParams powLimit, nPowTargetTimespan, nPowTargetSpacing, fPowAllowMinDifficultyBlocks, fPowNoRetargeting, enforce_BIP94, src/kernel/chainparams.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/kernel/chainparams.cpp

import Definitions.Def_BitcoinPow

theorem BitcoinPow.nextWork_permitted (height : Nat) (lastBits : BitVec 32) (lastTime firstTime : Int)
    (hh : height % BitcoinPow.difficultyAdjustmentInterval = 0)
    (hold : BitcoinPow.setCompact lastBits ≤ BitcoinPow.powLimit) :
    BitcoinPow.permittedTransition height lastBits
      (BitcoinPow.calculateNextWork lastBits lastTime firstTime) = true := by sorry
