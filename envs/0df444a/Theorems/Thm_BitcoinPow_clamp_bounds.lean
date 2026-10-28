-- Prove2me | Theorems.Thm_BitcoinPow_clamp_bounds
-- name    : BitcoinPow.clamp_bounds
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T04:28:57.905396+00:00
-- url     : https://prove2.me/theorems/e5f9d506-31c7-444d-9215-1a7089010d1e
-- title:
--   The retarget timespan is clamped to [T/4, 4T]
-- statement:
--   For every signed elapsed time $a \in \mathbb Z$, the clamped timespan used by `CalculateNextWorkRequired` satisfies
--   $$\frac{T}{4} = 302{,}400 \le \mathrm{clampTimespan}(a) \le 4T = 4{,}838{,}400,$$
--   with $T = 1{,}209{,}600$. Negative inputs, which arise when timestamps go backwards, are raised to $T/4$; this bounds every difficulty change to a factor of four in either direction.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: GetNextWorkRequired (lines 14-48), CalculateNextWorkRequired (50-85), PermittedDifficultyTransition (89-136), DeriveTarget (146-159), CheckProofOfWorkImpl (161-171), src/pow.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/pow.cpp; arith_uint256::SetCompact (176-194), GetCompact (196-216), base_uint::operator<<= (15-30), operator*=(uint32_t) (49-59), operator/= (77-104), bits() (205-218), src/arith_uint256.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/arith_uint256.cpp; CMainParams powLimit, nPowTargetTimespan, nPowTargetSpacing, fPowAllowMinDifficultyBlocks, fPowNoRetargeting, enforce_BIP94, src/kernel/chainparams.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/kernel/chainparams.cpp

import Definitions.Def_BitcoinPow

theorem BitcoinPow.clamp_bounds (actual : Int) :
    ((BitcoinPow.targetTimespan / 4 : Nat) : Int) ≤ BitcoinPow.clampTimespan actual ∧
    BitcoinPow.clampTimespan actual ≤ ((BitcoinPow.targetTimespan * 4 : Nat) : Int) := by sorry
