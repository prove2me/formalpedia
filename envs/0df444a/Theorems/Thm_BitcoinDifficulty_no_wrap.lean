-- Prove2me | Theorems.Thm_BitcoinDifficulty_no_wrap
-- name    : BitcoinDifficulty.no_wrap
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T13:49:40.800776+00:00
-- url     : https://prove2.me/theorems/f90e4417-3d7a-4c84-b015-906a083ae810
-- title:
--   A valid target times the clamped timespan never wraps around 2^256
-- statement:
--   For $t \le$ `powLimit` ($2^{224}-1$) and $ts \le 4{,}838{,}400$ (four times the target timespan): $t \cdot ts < 2^{256}$. The modular multiplication of `arith_uint256` is exact on every valid input.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: CalculateNextWorkRequired, GetNextWorkRequired, src/pow.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/pow.cpp; arith_uint256::SetCompact/GetCompact (arith_uint256.cpp); CMainParams (kernel/chainparams.cpp)

import Definitions.Def_BitcoinDifficulty
import Definitions.Def_BitcoinPow
open BitcoinDifficulty BitcoinPow

theorem BitcoinDifficulty.no_wrap (t : Nat) (ht : t ≤ BitcoinPow.powLimit) (ts : Nat) (hts : ts ≤ 4838400) :
    t * ts < BitcoinPow.width := by sorry
