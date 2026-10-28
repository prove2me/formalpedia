-- Prove2me | Theorems.Thm_BitcoinSubsidy_core_eq_spec
-- name    : BitcoinSubsidy.core_eq_spec
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T04:33:11.545989+00:00
-- url     : https://prove2.me/theorems/0d821956-780b-486c-8e28-fcd49cb14662
-- title:
--   Core block subsidy equals the halving schedule
-- statement:
--   For every block height $h \in \mathbb N$, the transcription of `GetBlockSubsidy` and the declarative halving schedule agree:
--   $$\mathrm{coreSubsidy}(h) = \left\lfloor \frac{50 \cdot \mathrm{COIN}}{2^{\lfloor h / 210000 \rfloor}} \right\rfloor .$$
--   On the left, $\mathrm{coreSubsidy}$ returns $0$ when $\lfloor h/210000 \rfloor \ge 64$ and otherwise right-shifts $50 \cdot \mathrm{COIN} = 5 \times 10^{9}$ by that many bits; on the right the schedule divides by the corresponding power of two.
--
--   The statement covers every height, including those where the source's `halvings >= 64` guard fires, where it asserts that the division already yields zero. It is the bridge that lets the remaining results be proved about the schedule and transferred to the implementation.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48, GetBlockSubsidy, src/validation.cpp lines 1833-1844: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp#L1833; COIN and MAX_MONEY, src/consensus/amount.h: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/amount.h; nSubsidyHalvingInterval = 210000, CMainParams, src/kernel/chainparams.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/kernel/chainparams.cpp

import Definitions.Def_BitcoinSubsidy

theorem BitcoinSubsidy.core_eq_spec (height : Nat) : coreSubsidy height = specSubsidy height := by sorry
