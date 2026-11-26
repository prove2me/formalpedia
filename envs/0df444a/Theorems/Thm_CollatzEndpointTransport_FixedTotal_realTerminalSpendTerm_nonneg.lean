-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_realTerminalSpendTerm_nonneg
-- name    : CollatzEndpointTransport.FixedTotal.realTerminalSpendTerm_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:34:20.622953+00:00
-- url     : https://prove2.me/theorems/b7309cfc-0f9e-5808-8949-77d9532a8ab6
-- title:
--   Fixed Total: real Terminal Spend Term nonneg
-- statement:
--   The Fixed Total construction uses the real Terminal Spend Term nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L321-L325
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L321-L325

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real NNReal
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.realTerminalSpendTerm_nonneg
    (theta : ℝ) (r D : ℕ) :
    0 ≤ realTerminalSpendTerm theta r D := by sorry
