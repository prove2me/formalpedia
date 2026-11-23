-- Prove2me | Theorems.Thm_Formalism_DimensionVariation_measurable_productCutoff
-- name    : Formalism.DimensionVariation.measurable_productCutoff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:55:11.7708+00:00
-- url     : https://prove2.me/theorems/45652b3d-7661-447b-9c79-0d003ada5f90
-- title:
--   Dimension Variation: measurable product Cutoff
-- statement:
--   The Dimension Variation construction uses the measurable product Cutoff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaSupremumBounds/GaussianShiftBounds/FockJet.lean#L118-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaSupremumBounds/GaussianShiftBounds/FockJet.lean#L118-L121

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

theorem Formalism.DimensionVariation.measurable_productCutoff {κ : Type} [Fintype κ] (N : ℕ) : Measurable (fjChiP (κ := κ) N) := by sorry
