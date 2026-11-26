-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_cosh_int_children
-- name    : FirstPassageLinearTransport.cosh_int_children
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:02:40.119371+00:00
-- url     : https://prove2.me/theorems/4d67e076-fcd6-4cb2-9017-842294b2b37a
-- title:
--   First Passage Linear Transport: cosh int children
-- statement:
--   The First Passage Linear Transport construction uses the cosh int children property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Barrier.lean#L102-L109
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Barrier.lean#L102-L109

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_Density
import Definitions.Def_FirstPassageLinearTransport_Barrier
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators

theorem FirstPassageLinearTransport.cosh_int_children (θ : ℝ) (y : ℤ) :
    Real.cosh (θ * ((y - 1 : ℤ) : ℝ)) +
        Real.cosh (θ * ((y + 1 : ℤ) : ℝ)) =
      2 * Real.cosh (θ * (y : ℝ)) * Real.cosh θ := by sorry
