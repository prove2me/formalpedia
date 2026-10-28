-- Prove2me | Theorems.Thm_BitcoinSubsidy_issuance_total
-- name    : BitcoinSubsidy.issuance_total
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T04:33:54.636839+00:00
-- url     : https://prove2.me/theorems/ce54c1ba-df71-4e52-b3e2-e5d34f816150
-- title:
--   Total issuance at the zero height
-- statement:
--   The cumulative subsidy of all blocks below the zero height is
--   $$\mathrm{issuedBelow}(6{,}930{,}000) = 2{,}099{,}999{,}997{,}690{,}000 \text{ satoshi},$$
--   that is, $20{,}999{,}999.9769$ bitcoin. Equivalently, $210{,}000 \cdot \sum_{j=0}^{32} \lfloor 5 \times 10^{9} / 2^{j} \rfloor = 210{,}000 \cdot 9{,}999{,}999{,}989$.
--
--   The figure falls $2{,}310{,}000$ satoshi short of twenty-one million bitcoin because each halving discards a remainder. Together with the extinction result it gives the exact total the schedule can ever issue.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48, GetBlockSubsidy, src/validation.cpp lines 1833-1844: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp#L1833; COIN and MAX_MONEY, src/consensus/amount.h: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/amount.h; nSubsidyHalvingInterval = 210000, CMainParams, src/kernel/chainparams.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/kernel/chainparams.cpp

import Definitions.Def_BitcoinSubsidy

theorem BitcoinSubsidy.issuance_total : issuedBelow zeroHeight = 2099999997690000 := by sorry
