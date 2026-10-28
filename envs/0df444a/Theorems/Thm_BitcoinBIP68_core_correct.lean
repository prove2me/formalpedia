-- Prove2me | Theorems.Thm_BitcoinBIP68_core_correct
-- name    : BitcoinBIP68.core_correct
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T01:36:02.324059+00:00
-- url     : https://prove2.me/theorems/59f7e227-715c-4993-8ee6-74ab3564d238
-- title:
--   Bitcoin Core sequence locks agree with the BIP68 specification
-- statement:
--   Let $v,f$ be unsigned 32-bit transaction-version and flag words, $H$ the candidate height, $M$ the supplied ancestor median-time function, and $I=[(s_i,c_i)]$ a finite input list. Assume $0<H\le2^{31}-1$, $c_i\le H$, and $0\le M(h)\le2^{63}-1$ for $h\le H$. For each non-disabled input when enforcement is active, also assume the pre-subtraction sum selected by bit 22 fits its signed destination: $c_i+d_i\le2^{31}-1$ when bit 22 is clear (height lock), and $M(\max(c_i-1,0))+512d_i\le2^{63}-1$ when bit 22 is set (time lock), with $d_i=s_i\bmod65536$. Each input is held to the bound of its own lock type, not to either bound.
--
--   Let $E$ mean $v\ge2$ and $f\bmod2=1$. Let $P(i)$ mean that bit 31 is set, or that the delay selected by bit 22 has elapsed: $c_i+d_i\le H$ for a height lock and $M(\max(c_i-1,0))+512d_i\le M(H-1)$ for a time lock. This component theorem has two conclusions:
--
--   $$\mathrm{SequenceLocks}_{\mathrm{Lean}}(v,f,H,M,I)=\mathrm{true}
--   \quad\Longleftrightarrow\quad \neg E\ \lor\ \forall i\in I,\ P(i),$$
--
--   and the returned height list is the original ordered list with $c_i$ replaced by zero exactly when $E$ holds and input $i$ has bit 31 set. No clock monotonicity, nonempty-list assumption, or prior acceptance assumption is imposed.
--
--   This is the correctness contract for a Lean transcription of the pinned Core helpers, relative to separately defined arithmetic eligibility and height-list specifications. Coinbase exclusion, supplying the ancestor clocks and spent-output heights, activation selection, and the manual C++-to-Lean correspondence are explicit external boundaries. It does not claim verification of a compiled Bitcoin Core binary.
--
--   Within the whole-mainnet mission this is a supporting component. Its caller assumptions must be discharged by the wider validation development; proving this theorem alone does not complete that mission.
-- source:
--   BIP68, Specification and Implementation: https://github.com/bitcoin/bips/blob/100ba872c808946155b1eeb8c4568058f2eea0a7/bip-0068.mediawiki; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48, CalculateSequenceLocks (lines 45–101), EvaluateSequenceLocks (103–111), SequenceLocks (113–116): https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/tx_verify.cpp#L45-L116. Functional contract extracted from these routines; the BIP does not number these claims as mathematical theorems.

import Definitions.Def_BIP68_Model
import Definitions.Def_BIP68_Core

theorem BitcoinBIP68.core_correct (version flags : BitVec 32)
    (ctx : BitcoinBIP68.Context) (inputs : List BitcoinBIP68.Input)
    (hctx : BitcoinBIP68.admissible ctx inputs)
    (hsafe : BitcoinBIP68.noOverflow version flags ctx inputs) :
    (BitcoinBIP68.sequenceLocks version flags ctx inputs = true ↔
      BitcoinBIP68.satisfiesBIP68 version flags ctx inputs) ∧
    BitcoinBIP68.returnedHeights (BitcoinBIP68.calculate version flags ctx inputs) =
      BitcoinBIP68.expectedHeights version flags inputs := by sorry
