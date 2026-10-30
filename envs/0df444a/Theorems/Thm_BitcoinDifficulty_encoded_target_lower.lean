-- Prove2me | Theorems.Thm_BitcoinDifficulty_encoded_target_lower
-- name    : BitcoinDifficulty.encoded_target_lower
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T13:50:22.45001+00:00
-- url     : https://prove2.me/theorems/8dabab88-ac13-4c8f-b1dd-84a6f8539f0b
-- title:
--   The encoded target drops by at most a factor of four per period, up to rounding
-- statement:
--   For `setCompact bits ≤ powLimit` and any timestamps: `setCompact (getCompact (setCompact bits / 4)) ≤ setCompact (calculateNextWork bits lastTime firstTime)`. The new target is at least the compact encoding of a quarter of the old one (`round_mono`).
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: CalculateNextWorkRequired, GetNextWorkRequired, src/pow.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/pow.cpp; arith_uint256::SetCompact/GetCompact (arith_uint256.cpp); CMainParams (kernel/chainparams.cpp)

import Definitions.Def_BitcoinDifficulty
import Definitions.Def_BitcoinPow
open BitcoinDifficulty BitcoinPow

theorem BitcoinDifficulty.encoded_target_lower (bits : BitVec 32) (hb : BitcoinPow.setCompact bits ≤ BitcoinPow.powLimit)
    (lastTime firstTime : Int) :
    BitcoinPow.setCompact (BitcoinPow.getCompact (BitcoinPow.setCompact bits / 4)) ≤
      BitcoinPow.setCompact (BitcoinPow.calculateNextWork bits lastTime firstTime) := by sorry
