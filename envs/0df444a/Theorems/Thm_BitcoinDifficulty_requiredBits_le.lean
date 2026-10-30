-- Prove2me | Theorems.Thm_BitcoinDifficulty_requiredBits_le
-- name    : BitcoinDifficulty.requiredBits_le
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T13:50:57.904167+00:00
-- url     : https://prove2.me/theorems/81ebe357-77b4-44c0-8bb6-fca6cad5b463
-- title:
--   Timewarp bound: the next required target is at most four times the tip's
-- statement:
--   For any chain state whose tip target is valid (`setCompact (tip bits) ≤ powLimit`): `setCompact S.requiredBits ≤ 4 · setCompact (tip bits)`, whether or not the next block is at a retarget boundary, whatever the timestamps of the period's blocks. This is the whole of what an adversary who controls timestamps can do to the difficulty in one period under the mainnet rules: lower it by at most a factor of four (and, by `encoded_target_lower`, raise it by at most a factor of four); the known timewarp attack is the repetition of this bound across periods, which `target_after_upper` quantifies.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: CalculateNextWorkRequired, GetNextWorkRequired, src/pow.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/pow.cpp; arith_uint256::SetCompact/GetCompact (arith_uint256.cpp); CMainParams (kernel/chainparams.cpp)

import Definitions.Def_BitcoinDifficulty
import Definitions.Def_BitcoinPow
open BitcoinDifficulty BitcoinPow

theorem BitcoinDifficulty.requiredBits_le (S : BitcoinBlockV2.ChainState)
    (hb : BitcoinPow.setCompact (BitVec.ofNat 32 S.tip.bits) ≤ BitcoinPow.powLimit) :
    BitcoinPow.setCompact S.requiredBits ≤ 4 * BitcoinPow.setCompact (BitVec.ofNat 32 S.tip.bits) := by sorry
