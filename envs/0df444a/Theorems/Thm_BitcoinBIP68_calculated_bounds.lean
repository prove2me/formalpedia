-- Prove2me | Theorems.Thm_BitcoinBIP68_calculated_bounds
-- name    : BitcoinBIP68.calculated_bounds
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T01:35:52.027696+00:00
-- url     : https://prove2.me/theorems/4a25218e-fba1-43d6-938e-ead5db5381f9
-- title:
--   Calculated lock thresholds fit their signed destinations
-- statement:
--   Let version and flags be arbitrary unsigned 32-bit words. Let a context and finite input list satisfy the admissible-domain conditions: $0<H\le2^{31}-1$, every input height at most $H$, and nonnegative supplied ancestor clocks at most $2^{63}-1$. Assume additionally that every actually enforced, non-disabled height sum $c+d$ fits $2^{31}-1$, and every actually enforced, non-disabled time sum $M(\max(c-1,0))+512d$ fits $2^{63}-1$. These are bounds before subtraction of one, selected according to bit 22.
--
--   If calculation returns thresholds $a,b$, then
--
--   $$-1\le a\le2^{31}-1\quad\land\quad-1\le b\le2^{63}-1.$$
--
--   Disabled inputs and disabled enforcement require no delay-sum bounds. Empty lists and zero delays are included. The result supplies range guarantees for the mathematical-integer model on the explicitly stated domain; it is not a theorem that the entire C++ caller always establishes that domain.
-- source:
--   BIP68, Specification and Implementation: https://github.com/bitcoin/bips/blob/100ba872c808946155b1eeb8c4568058f2eea0a7/bip-0068.mediawiki; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48, CalculateSequenceLocks (lines 45–101), EvaluateSequenceLocks (103–111), SequenceLocks (113–116): https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/tx_verify.cpp#L45-L116. Functional contract extracted from these routines; the BIP does not number these claims as mathematical theorems.

import Definitions.Def_BIP68_Model
import Definitions.Def_BIP68_Core

theorem BitcoinBIP68.calculated_bounds (version flags : BitVec 32)
    (ctx : BitcoinBIP68.Context) (inputs : List BitcoinBIP68.Input)
    (hctx : BitcoinBIP68.admissible ctx inputs)
    (hsafe : BitcoinBIP68.noOverflow version flags ctx inputs) :
    let result := BitcoinBIP68.calculate version flags ctx inputs
    (-1 ≤ result.minHeight ∧ result.minHeight ≤ (BitcoinBIP68.int32Max : Int)) ∧
    (-1 ≤ result.minTime ∧ result.minTime ≤ (BitcoinBIP68.int64Max : Int)) := by sorry
