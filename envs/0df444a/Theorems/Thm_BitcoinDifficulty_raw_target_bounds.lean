-- Prove2me | Theorems.Thm_BitcoinDifficulty_raw_target_bounds
-- name    : BitcoinDifficulty.raw_target_bounds
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T13:49:52.660141+00:00
-- url     : https://prove2.me/theorems/0aa3a549-a0d9-4692-952f-3421cbeaebeb
-- title:
--   The raw next target is between a quarter and four times the last target
-- statement:
--   For a last target $t \le$ `powLimit` and any timestamps: `rawNextTarget t lastTime firstTime` $\le 4t$, and either the cap binds (the raw target is `powLimit`) or `rawNextTarget t lastTime firstTime` $\ge \lfloor t/4 \rfloor$. From the clamp bounds of the proof-of-work mission and the exact arithmetic.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: CalculateNextWorkRequired, GetNextWorkRequired, src/pow.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/pow.cpp; arith_uint256::SetCompact/GetCompact (arith_uint256.cpp); CMainParams (kernel/chainparams.cpp)

import Definitions.Def_BitcoinDifficulty
import Definitions.Def_BitcoinPow
open BitcoinDifficulty BitcoinPow

theorem BitcoinDifficulty.raw_target_bounds (t : Nat) (ht : t ≤ BitcoinPow.powLimit) (lastTime firstTime : Int) :
    BitcoinDifficulty.rawNextTarget t lastTime firstTime ≤ 4 * t ∧
    (BitcoinDifficulty.rawNextTarget t lastTime firstTime = BitcoinPow.powLimit ∨
      t / 4 ≤ BitcoinDifficulty.rawNextTarget t lastTime firstTime) := by sorry
