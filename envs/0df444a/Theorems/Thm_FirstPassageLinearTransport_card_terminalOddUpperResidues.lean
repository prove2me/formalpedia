-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_card_terminalOddUpperResidues
-- name    : FirstPassageLinearTransport.card_terminalOddUpperResidues
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:40:35.117644+00:00
-- url     : https://prove2.me/theorems/c5b7a8fd-d12a-4900-8ad8-24589b89e23d
-- title:
--   First Passage Linear Transport: card terminal Odd Upper Residues
-- statement:
--   Exact binomial law for the terminal odd count on a complete residue
--   block.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutDensity.lean#L440-L455
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutDensity.lean#L440-L455

import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.card_terminalOddUpperResidues {m k : ℕ} (hk : k ≤ m) :
    (terminalOddUpperResidues m k).card = binomialUpperTail m k := by sorry
