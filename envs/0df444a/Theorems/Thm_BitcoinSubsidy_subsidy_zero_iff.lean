-- Prove2me | Theorems.Thm_BitcoinSubsidy_subsidy_zero_iff
-- name    : BitcoinSubsidy.subsidy_zero_iff
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T04:33:45.477511+00:00
-- url     : https://prove2.me/theorems/50c6b0f4-bfb0-4dfd-ae73-a8242df4225d
-- title:
--   The subsidy is zero exactly from the thirty-third halving
-- statement:
--   For every block height $h \in \mathbb N$,
--   $$\mathrm{coreSubsidy}(h) = 0 \iff h \ge 33 \cdot 210000 = 6{,}930{,}000 .$$
--   Both directions are asserted. Below the zero height the subsidy is positive; in particular it equals one satoshi throughout the thirty-third interval (heights $6{,}720{,}000$ to $6{,}929{,}999$), since $\lfloor 5 \times 10^{9} / 2^{32} \rfloor = 1$. From the zero height on it is zero, since $5 \times 10^{9} < 2^{33}$. The source's `halvings >= 64` guard is therefore never the operative reason for a zero subsidy.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48, GetBlockSubsidy, src/validation.cpp lines 1833-1844: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp#L1833; COIN and MAX_MONEY, src/consensus/amount.h: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/amount.h; nSubsidyHalvingInterval = 210000, CMainParams, src/kernel/chainparams.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/kernel/chainparams.cpp

import Definitions.Def_BitcoinSubsidy

theorem BitcoinSubsidy.subsidy_zero_iff (height : Nat) :
    coreSubsidy height = 0 ↔ zeroHeight ≤ height := by sorry
