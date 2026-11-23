-- Prove2me | Theorems.Thm_Formalism_DimensionVariation_fjPolydisc
-- name    : Formalism.DimensionVariation.fjPolydisc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:10:28.613719+00:00
-- url     : https://prove2.me/theorems/c8f85400-cf6f-4a34-97d8-f083edfa9bff
-- title:
--   Dimension Variation: fj Polydisc
-- statement:
--   The Dimension Variation construction uses the fj Polydisc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaSupremumBounds/GaussianShiftBounds/FockJet.lean#L263-L316
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaSupremumBounds/GaussianShiftBounds/FockJet.lean#L263-L316

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

theorem Formalism.DimensionVariation.fjPolydisc {κ : Type} [Fintype κ] (F : (κ → ℂ) → ℂ) (c : (κ → ℕ) → ℂ)
    (hs : ∀ u, HasSum (fun e => c e * mono u e) (F u)) (e : κ → ℕ) (N : ℕ) :
    ∫ u : κ → ℂ, fjChiP N u * (F u * mono (cj u) e * (Real.exp (-(nsq u)) : ℂ)) =
      c e * ∫ u : κ → ℂ, fjChiP N u * (mono u e * mono (cj u) e * (Real.exp (-(nsq u)) : ℂ)) := by sorry
