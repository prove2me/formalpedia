-- Prove2me | Theorems.Thm_BitcoinSubsidy_subsidy_antitone
-- name    : BitcoinSubsidy.subsidy_antitone
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T04:33:28.238021+00:00
-- url     : https://prove2.me/theorems/51ca1f05-023d-4d97-94cf-856191f6a31d
-- title:
--   The block subsidy never increases with height
-- statement:
--   For all block heights $h_1 \le h_2$,
--   $$\mathrm{coreSubsidy}(h_2) \le \mathrm{coreSubsidy}(h_1).$$
--   The subsidy is a non-increasing function of height: it is constant within each interval of $210{,}000$ blocks and drops at each interval boundary. The inequality is not strict, since consecutive heights within an interval share the same subsidy.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48, GetBlockSubsidy, src/validation.cpp lines 1833-1844: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp#L1833; COIN and MAX_MONEY, src/consensus/amount.h: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/amount.h; nSubsidyHalvingInterval = 210000, CMainParams, src/kernel/chainparams.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/kernel/chainparams.cpp

import Definitions.Def_BitcoinSubsidy

theorem BitcoinSubsidy.subsidy_antitone (h₁ h₂ : Nat) (h : h₁ ≤ h₂) :
    coreSubsidy h₂ ≤ coreSubsidy h₁ := by sorry
