-- Prove2me | Theorems.Thm_BitcoinBIP68_fold_acceptance
-- name    : BitcoinBIP68.fold_acceptance
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T01:35:31.485324+00:00
-- url     : https://prove2.me/theorems/07ddff3c-07ba-4617-9162-65af213651d6
-- title:
--   The sequence-lock fold enforces exactly the input constraints
-- statement:
--   Let $H$ be any natural-number height, let $M:\mathbb N\to\mathbb N$ be any clock function, let $I$ be any finite input list, and let $A$ be any accumulator with two integer bounds and any auxiliary height list. Write $F(A,I)$ for the left-to-right Core input fold, and $P(i)$ for the declarative input condition: an input is disabled, or its selected height/time delay has elapsed. Evaluation means that both stored bounds are strictly below $H$ and $M(\max(H-1,0))$, respectively. Then
--
--   $$\mathrm{evaluate}(F(A,I))=\mathrm{true}\quad\Longleftrightarrow\quad
--   \mathrm{evaluate}(A)=\mathrm{true}\ \land\ \forall i\in I,\ P(i).$$
--
--   There are no range, positivity, clock-monotonicity, or ancestor-height hypotheses in this mathematical fold contract. In particular, the initial accumulator need not be the sentinel state. The empty list gives the identity case. This result characterizes accumulation of both kinds of relative delay without assuming they are already satisfied.
-- source:
--   BIP68, Specification and Implementation: https://github.com/bitcoin/bips/blob/100ba872c808946155b1eeb8c4568058f2eea0a7/bip-0068.mediawiki; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48, CalculateSequenceLocks (lines 45–101), EvaluateSequenceLocks (103–111), SequenceLocks (113–116): https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/tx_verify.cpp#L45-L116. Functional contract extracted from these routines; the BIP does not number these claims as mathematical theorems.

import Definitions.Def_BIP68_Model
import Definitions.Def_BIP68_Core

theorem BitcoinBIP68.fold_acceptance (ctx : BitcoinBIP68.Context)
    (acc : BitcoinBIP68.Accumulator) (inputs : List BitcoinBIP68.Input) :
    BitcoinBIP68.evaluate ctx (inputs.foldl (BitcoinBIP68.coreStep ctx) acc) = true ↔
      BitcoinBIP68.evaluate ctx acc = true ∧
      ∀ input ∈ inputs, BitcoinBIP68.inputSatisfied ctx input := by sorry
