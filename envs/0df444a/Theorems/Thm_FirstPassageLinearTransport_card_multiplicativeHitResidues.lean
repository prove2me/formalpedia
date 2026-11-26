-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_card_multiplicativeHitResidues
-- name    : FirstPassageLinearTransport.card_multiplicativeHitResidues
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:22:09.325156+00:00
-- url     : https://prove2.me/theorems/7173c558-29f0-5c07-9aff-38f907e2481d
-- title:
--   First Passage Linear Transport: card multiplicative Hit Residues
-- statement:
--   The First Passage Linear Transport construction uses the card multiplicative Hit Residues property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/OrbitCeiling.lean#L155-L163
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/OrbitCeiling.lean#L155-L163

import Definitions.Def_FirstPassageLinearTransport_NaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Definitions.Def_FirstPassageLinearTransport_RawDynamics
import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.card_multiplicativeHitResidues (M : ℕ) (u : ℝ) :
    (multiplicativeHitResidues M u).card =
      multiplicativeHitCount u M 1 := by sorry
