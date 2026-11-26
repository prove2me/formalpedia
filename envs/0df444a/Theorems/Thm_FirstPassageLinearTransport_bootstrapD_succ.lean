-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_bootstrapD_succ
-- name    : FirstPassageLinearTransport.bootstrapD_succ
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:34:46.587789+00:00
-- url     : https://prove2.me/theorems/b4ee97e8-ec1c-4356-a6e2-809940f49c1d
-- title:
--   First Passage Linear Transport: bootstrap D succ
-- statement:
--   The First Passage Linear Transport construction uses the bootstrap D succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Bootstrap.lean#L41-L44
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Bootstrap.lean#L41-L44

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_FirstPassageLinearTransport_Parameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_Bootstrap
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
noncomputable section

theorem FirstPassageLinearTransport.bootstrapD_succ (chi Dc : ℝ) (R : ℕ) :
    bootstrapD chi Dc (R + 1) = chi * bootstrapD chi Dc R := by sorry
