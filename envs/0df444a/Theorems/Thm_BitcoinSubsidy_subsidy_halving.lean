-- Prove2me | Theorems.Thm_BitcoinSubsidy_subsidy_halving
-- name    : BitcoinSubsidy.subsidy_halving
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T04:33:37.046053+00:00
-- url     : https://prove2.me/theorems/073d335c-19c1-46c4-add9-2a8b138af73f
-- title:
--   Advancing one interval halves the subsidy
-- statement:
--   For every block height $h \in \mathbb N$,
--   $$\mathrm{coreSubsidy}(h + 210000) = \left\lfloor \frac{\mathrm{coreSubsidy}(h)}{2} \right\rfloor .$$
--   Moving forward by exactly one halving interval halves the subsidy, with the remainder discarded. This is the defining recurrence of the schedule stated directly on the implementation; iterating it from height $0$ reproduces the sequence $50, 25, 12.5, \dots$ bitcoin.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48, GetBlockSubsidy, src/validation.cpp lines 1833-1844: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp#L1833; COIN and MAX_MONEY, src/consensus/amount.h: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/amount.h; nSubsidyHalvingInterval = 210000, CMainParams, src/kernel/chainparams.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/kernel/chainparams.cpp

import Definitions.Def_BitcoinSubsidy

theorem BitcoinSubsidy.subsidy_halving (height : Nat) :
    coreSubsidy (height + halvingInterval) = coreSubsidy height / 2 := by sorry
