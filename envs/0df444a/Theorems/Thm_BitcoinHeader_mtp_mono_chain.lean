-- Prove2me | Theorems.Thm_BitcoinHeader_mtp_mono_chain
-- name    : BitcoinHeader.mtp_mono_chain
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T04:19:09.326324+00:00
-- url     : https://prove2.me/theorems/2c963699-42ff-43a2-b748-f3291f782d31
-- title:
--   Median time past is non-decreasing along a chain obeying time-too-old
-- statement:
--   Let $t_0, t_1, \dots, t_{n-1}$ be the block times of a chain, most recent first, such that every block satisfies the `time-too-old` rule against its predecessor:
--   $$\forall i < n,\quad \mathrm{MTP}(t_{i+1}, t_{i+2}, \dots) < t_i .$$
--   Then for all $i \le j \le n$,
--   $$\mathrm{MTP}(t_j, t_{j+1}, \dots) \le \mathrm{MTP}(t_i, t_{i+1}, \dots):$$
--   the median time past of any ancestor is at most that of any descendant. Here $\mathrm{MTP}$ is the transcription of `GetMedianTimePast`: the element at index $\lfloor |w|/2 \rfloor$ of the sorted window of at most eleven most recent times.
--
--   This is the clock-monotonicity property that time-based lock-times (BIP113, BIP68) rely on: once the chain's median time has passed a threshold, it never falls back below it. The chain's times themselves need not be increasing; only the median rule is assumed.
--
--   **Formalization Note.** The statement is about suffixes `times.drop i` of the time list; the hypothesis is the `time-too-old` conjunct of `ContextualCheckBlockHeader` at every position.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: CBlockIndex::GetMedianTimePast and nMedianTimeSpan, MAX_FUTURE_BLOCK_TIME, src/chain.h: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/chain.h; ContextualCheckBlockHeader, src/validation.cpp (lines 4091-4128): https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; DeploymentActiveAfter (buried), src/deploymentstatus.h; BIP34Height, BIP66Height, BIP65Height in CMainParams, src/kernel/chainparams.cpp

import Definitions.Def_BitcoinHeader

theorem BitcoinHeader.mtp_mono_chain (times : List Int)
    (hok : ∀ (i : Nat) (hi : i < times.length),
      BitcoinHeader.medianTimePast (times.drop (i + 1)) < times[i]) :
    ∀ (i j : Nat), i ≤ j → j ≤ times.length →
      BitcoinHeader.medianTimePast (times.drop j) ≤ BitcoinHeader.medianTimePast (times.drop i) := by sorry
