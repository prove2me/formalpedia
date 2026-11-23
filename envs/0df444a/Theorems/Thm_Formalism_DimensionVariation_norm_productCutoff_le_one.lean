-- Prove2me | Theorems.Thm_Formalism_DimensionVariation_norm_productCutoff_le_one
-- name    : Formalism.DimensionVariation.norm_productCutoff_le_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:11:13.60983+00:00
-- url     : https://prove2.me/theorems/cea96704-9bcf-48f6-b4dd-5bdb7adf32f1
-- title:
--   Dimension Variation: norm product Cutoff le one
-- statement:
--   The Dimension Variation construction uses the norm product Cutoff le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaSupremumBounds/GaussianShiftBounds/FockJet.lean#L123-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaSupremumBounds/GaussianShiftBounds/FockJet.lean#L123-L125

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

theorem Formalism.DimensionVariation.norm_productCutoff_le_one {κ : Type} [Fintype κ] (N : ℕ) (u : κ → ℂ) : ‖fjChiP N u‖ ≤ 1 := by sorry
