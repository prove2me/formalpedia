-- Prove2me | Theorems.Thm_BitcoinPow_checkProofOfWork_iff
-- name    : BitcoinPow.checkProofOfWork_iff
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T04:28:21.556821+00:00
-- url     : https://prove2.me/theorems/b69a34b7-d28b-4290-aff3-0529bc50d4dd
-- title:
--   Proof-of-work acceptance, characterized
-- statement:
--   For every hash value $h \in \mathbb N$ and every 32-bit word $c$,
--   $$\mathrm{checkProofOfWork}(h, c) = \mathtt{true} \iff \neg\mathrm{negative}(c) \wedge \neg\mathrm{overflow}(c) \wedge 0 < \mathrm{specTarget}(c) \wedge \mathrm{specTarget}(c) \le 2^{224}-1 \wedge h \le \mathrm{specTarget}(c).$$
--   This is `DeriveTarget` followed by the comparison in `CheckProofOfWorkImpl`, restated on the exact value of the word. A header passes exactly when its `nBits` is a well-formed, in-range, positive target and the hash is at most that target.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: GetNextWorkRequired (lines 14-48), CalculateNextWorkRequired (50-85), PermittedDifficultyTransition (89-136), DeriveTarget (146-159), CheckProofOfWorkImpl (161-171), src/pow.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/pow.cpp; arith_uint256::SetCompact (176-194), GetCompact (196-216), base_uint::operator<<= (15-30), operator*=(uint32_t) (49-59), operator/= (77-104), bits() (205-218), src/arith_uint256.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/arith_uint256.cpp; CMainParams powLimit, nPowTargetTimespan, nPowTargetSpacing, fPowAllowMinDifficultyBlocks, fPowNoRetargeting, enforce_BIP94, src/kernel/chainparams.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/kernel/chainparams.cpp

import Definitions.Def_BitcoinPow

theorem BitcoinPow.checkProofOfWork_iff (hash : Nat) (nBits : BitVec 32) :
    BitcoinPow.checkProofOfWork hash nBits = true ↔
      BitcoinPow.compactNegative nBits = false ∧ BitcoinPow.compactOverflow nBits = false ∧
      0 < BitcoinPow.specTarget nBits ∧ BitcoinPow.specTarget nBits ≤ BitcoinPow.powLimit ∧
      hash ≤ BitcoinPow.specTarget nBits := by sorry
