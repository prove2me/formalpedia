-- Prove2me | Theorems.Thm_BitcoinDifficulty_target_after_le_powLimit
-- name    : BitcoinDifficulty.target_after_le_powLimit
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T13:50:46.062131+00:00
-- url     : https://prove2.me/theorems/a74033f3-a63a-4492-a4e8-b290dccdafc6
-- title:
--   The target never exceeds powLimit
-- statement:
--   For `setCompact bits ≤ powLimit` and any list of periods: `setCompact (targetAfter bits periods) ≤ powLimit`.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: CalculateNextWorkRequired, GetNextWorkRequired, src/pow.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/pow.cpp; arith_uint256::SetCompact/GetCompact (arith_uint256.cpp); CMainParams (kernel/chainparams.cpp)

import Definitions.Def_BitcoinDifficulty
import Definitions.Def_BitcoinPow
open BitcoinDifficulty BitcoinPow

theorem BitcoinDifficulty.target_after_le_powLimit (bits : BitVec 32) (hb : BitcoinPow.setCompact bits ≤ BitcoinPow.powLimit) :
    ∀ (periods : List (Int × Int)), BitcoinPow.setCompact (BitcoinDifficulty.targetAfter bits periods) ≤ BitcoinPow.powLimit := by sorry
