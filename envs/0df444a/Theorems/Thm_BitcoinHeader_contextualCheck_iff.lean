-- Prove2me | Theorems.Thm_BitcoinHeader_contextualCheck_iff
-- name    : BitcoinHeader.contextualCheck_iff
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T04:18:49.550842+00:00
-- url     : https://prove2.me/theorems/016848c4-b81d-41e0-b8fb-5e26fa95adc0
-- title:
--   Acceptance by the contextual header check, characterized
-- statement:
--   For every header $h$, previous height $p$, chain of previous times, required `nBits` $r$ and local time $now$, the contextual check accepts exactly when
--   $$h.\mathrm{bits} = r \;\wedge\; \mathrm{MTP}(\text{prevTimes}) < h.\mathrm{time} \;\wedge\; h.\mathrm{time} \le now + 7{,}200 \;\wedge\; \neg\,\mathrm{outdated},$$
--   where outdated is the disjunction of the three version-floor conditions. These are the `bad-diffbits`, `time-too-old`, `time-too-new` and `bad-version` rejections of `ContextualCheckBlockHeader`.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: CBlockIndex::GetMedianTimePast and nMedianTimeSpan, MAX_FUTURE_BLOCK_TIME, src/chain.h: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/chain.h; ContextualCheckBlockHeader, src/validation.cpp (lines 4091-4128): https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; DeploymentActiveAfter (buried), src/deploymentstatus.h; BIP34Height, BIP66Height, BIP65Height in CMainParams, src/kernel/chainparams.cpp

import Definitions.Def_BitcoinHeader

theorem BitcoinHeader.contextualCheck_iff (h : BitcoinHeader.Header) (prevHeight : Nat) (prevTimes : List Int)
    (required : BitVec 32) (now : Int) :
    BitcoinHeader.contextualCheck h prevHeight prevTimes required now = true ↔
      h.bits = required ∧
      BitcoinHeader.medianTimePast prevTimes < h.time ∧
      h.time ≤ now + BitcoinHeader.MAX_FUTURE_BLOCK_TIME ∧
      ¬ ((h.version < 2 ∧ BitcoinHeader.BIP34Height ≤ prevHeight + 1) ∨
         (h.version < 3 ∧ BitcoinHeader.BIP66Height ≤ prevHeight + 1) ∨
         (h.version < 4 ∧ BitcoinHeader.BIP65Height ≤ prevHeight + 1)) := by sorry
