-- Prove2me | Theorems.Thm_BitcoinDifficulty_target_after_upper
-- name    : BitcoinDifficulty.target_after_upper
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T13:50:33.607172+00:00
-- url     : https://prove2.me/theorems/796bbe1c-2917-42b6-8710-84fa5055f76d
-- title:
--   Over m periods the target grows by at most 4^m
-- statement:
--   For `setCompact bits ≤ powLimit` and any list of $m$ periods with any timestamps: `setCompact (targetAfter bits periods) ≤ 4^m · setCompact bits`.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: CalculateNextWorkRequired, GetNextWorkRequired, src/pow.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/pow.cpp; arith_uint256::SetCompact/GetCompact (arith_uint256.cpp); CMainParams (kernel/chainparams.cpp)

import Definitions.Def_BitcoinDifficulty
import Definitions.Def_BitcoinPow
open BitcoinDifficulty BitcoinPow

theorem BitcoinDifficulty.target_after_upper (bits : BitVec 32) (hb : BitcoinPow.setCompact bits ≤ BitcoinPow.powLimit) :
    ∀ (periods : List (Int × Int)),
    BitcoinPow.setCompact (BitcoinDifficulty.targetAfter bits periods) ≤ 4 ^ periods.length * BitcoinPow.setCompact bits := by sorry
