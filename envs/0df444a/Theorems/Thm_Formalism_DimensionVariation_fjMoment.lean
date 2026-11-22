-- Prove2me | Theorems.Thm_Formalism_DimensionVariation_fjMoment
-- name    : Formalism.DimensionVariation.fjMoment
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:06:08.906804+00:00
-- url     : https://prove2.me/theorems/dcd668f3-2bf2-4d72-99fd-c11627b0e220
-- title:
--   Dimension Variation: fj Moment
-- statement:
--   The Dimension Variation construction uses the fj Moment property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaSupremumBounds/GaussianShiftBounds/FockJet.lean#L11-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaSupremumBounds/GaussianShiftBounds/FockJet.lean#L11-L26

import Mathlib
import Definitions.Def_Formalism_ThetaSupremumBounds_StatementA
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_FockJet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset MeasureTheory Filter Topology
open scoped ComplexConjugate Real Nat
noncomputable section
open Formalism Formalism.DimensionVariation

theorem Formalism.DimensionVariation.fjMoment (b : ℝ) (hb : 0 < b) (n : ℕ) :
    Integrable (fun z : ℂ => ‖z‖ ^ n * Real.exp (-b * ‖z‖ ^ 2)) ∧
    ∫ z : ℂ, ‖z‖ ^ n * Real.exp (-b * ‖z‖ ^ 2) =
      π * b ^ (-((n : ℝ) + 2) / 2) * Real.Gamma (((n : ℝ) + 2) / 2) := by sorry
