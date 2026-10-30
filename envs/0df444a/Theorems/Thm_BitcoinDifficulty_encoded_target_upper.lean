-- Prove2me | Theorems.Thm_BitcoinDifficulty_encoded_target_upper
-- name    : BitcoinDifficulty.encoded_target_upper
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T13:50:07.055453+00:00
-- url     : https://prove2.me/theorems/b522eb55-182e-4def-8933-d10e64b1da3d
-- title:
--   The encoded target at most quadruples per period
-- statement:
--   For `setCompact bits ≤ powLimit` and any timestamps: `setCompact (calculateNextWork bits lastTime firstTime) ≤ 4 · setCompact bits`. The compact encoding rounds down (`getCompact_le`).
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: CalculateNextWorkRequired, GetNextWorkRequired, src/pow.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/pow.cpp; arith_uint256::SetCompact/GetCompact (arith_uint256.cpp); CMainParams (kernel/chainparams.cpp)

import Definitions.Def_BitcoinDifficulty
import Definitions.Def_BitcoinPow
open BitcoinDifficulty BitcoinPow

theorem BitcoinDifficulty.encoded_target_upper (bits : BitVec 32) (hb : BitcoinPow.setCompact bits ≤ BitcoinPow.powLimit)
    (lastTime firstTime : Int) :
    BitcoinPow.setCompact (BitcoinPow.calculateNextWork bits lastTime firstTime) ≤ 4 * BitcoinPow.setCompact bits := by sorry
