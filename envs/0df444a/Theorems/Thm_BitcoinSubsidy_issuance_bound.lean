-- Prove2me | Theorems.Thm_BitcoinSubsidy_issuance_bound
-- name    : BitcoinSubsidy.issuance_bound
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T04:34:19.335058+00:00
-- url     : https://prove2.me/theorems/f37bf11e-f4aa-44e0-b59a-78081601c7b9
-- title:
--   Total block subsidy stays below MAX_MONEY
-- statement:
--   For every $n \in \mathbb N$, the cumulative subsidy of all blocks at heights below $n$ is strictly less than the consensus amount bound:
--   $$\mathrm{issuedBelow}(n) < \mathrm{MAX\_MONEY} = 21{,}000{,}000 \cdot 10^{8}.$$
--   Here $\mathrm{issuedBelow}(n) = \sum_{h < n} \mathrm{coreSubsidy}(h)$ with $\mathrm{coreSubsidy}$ the transcription of `GetBlockSubsidy` at mainnet parameters.
--
--   This is the arithmetic content of the twenty-one-million cap: no chain length, however long, lets the subsidy schedule issue `MAX_MONEY` or more. It is stated as a strict inequality against the named constant rather than as an exact value, so that it is the weakest statement a ledger-supply argument needs and remains true under any refinement of the exact total.
--
--   **Formalization Note.** The bound concerns the subsidy schedule only. Fees, unclaimed coinbase value and unspendable outputs are matters for the UTXO transition and are not modeled here.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48, GetBlockSubsidy, src/validation.cpp lines 1833-1844: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp#L1833; COIN and MAX_MONEY, src/consensus/amount.h: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/amount.h; nSubsidyHalvingInterval = 210000, CMainParams, src/kernel/chainparams.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/kernel/chainparams.cpp

import Definitions.Def_BitcoinSubsidy

theorem BitcoinSubsidy.issuance_bound (n : Nat) : issuedBelow n < MAX_MONEY := by sorry
