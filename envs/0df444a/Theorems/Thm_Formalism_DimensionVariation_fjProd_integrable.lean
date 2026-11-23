-- Prove2me | Theorems.Thm_Formalism_DimensionVariation_fjProd_integrable
-- name    : Formalism.DimensionVariation.fjProd_integrable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:10:49.361736+00:00
-- url     : https://prove2.me/theorems/9028e9a4-1578-4107-8dfb-5e854989c9c5
-- title:
--   Dimension Variation: fj Prod integrable
-- statement:
--   The Dimension Variation construction uses the fj Prod integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaSupremumBounds/GaussianShiftBounds/FockJet.lean#L158-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaSupremumBounds/GaussianShiftBounds/FockJet.lean#L158-L162

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

theorem Formalism.DimensionVariation.fjProd_integrable {κ : Type} [Fintype κ] (a b : κ → ℕ) :
    Integrable (fun u : κ → ℂ => mono u a * mono (cj u) b * (Real.exp (-(nsq u)) : ℂ)) := by sorry
