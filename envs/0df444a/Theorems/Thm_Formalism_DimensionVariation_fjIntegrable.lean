-- Prove2me | Theorems.Thm_Formalism_DimensionVariation_fjIntegrable
-- name    : Formalism.DimensionVariation.fjIntegrable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:54:02.820717+00:00
-- url     : https://prove2.me/theorems/3e1b7a9c-ea7a-45a3-b27d-13524174dc97
-- title:
--   Dimension Variation: fj Integrable
-- statement:
--   The Dimension Variation construction uses the fj Integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaSupremumBounds/GaussianShiftBounds/FockJet.lean#L217-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaSupremumBounds/GaussianShiftBounds/FockJet.lean#L217-L253

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

theorem Formalism.DimensionVariation.fjIntegrable {κ : Type} [Fintype κ] (F : (κ → ℂ) → ℂ) (S : ℝ) (hF : Continuous F)
    (hg : ∀ u, ‖F u‖ ≤ S * Real.exp (nsq u / 2)) (e : κ → ℕ) :
    Integrable (fun u : κ → ℂ => F u * mono (cj u) e * (Real.exp (-(nsq u)) : ℂ)) := by sorry
