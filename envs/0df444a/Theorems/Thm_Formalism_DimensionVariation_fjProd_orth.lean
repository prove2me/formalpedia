-- Prove2me | Theorems.Thm_Formalism_DimensionVariation_fjProd_orth
-- name    : Formalism.DimensionVariation.fjProd_orth
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:10:40.768725+00:00
-- url     : https://prove2.me/theorems/78dda83e-fa69-4384-9f10-601558cfe36f
-- title:
--   Dimension Variation: fj Prod orth
-- statement:
--   The Dimension Variation construction uses the fj Prod orth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaSupremumBounds/GaussianShiftBounds/FockJet.lean#L175-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaSupremumBounds/GaussianShiftBounds/FockJet.lean#L175-L189

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

theorem Formalism.DimensionVariation.fjProd_orth {κ : Type} [Fintype κ] (N : ℕ) (a b : κ → ℕ) (hab : a ≠ b) :
    ∫ u : κ → ℂ, fjChiP N u * (mono u a * mono (cj u) b * (Real.exp (-(nsq u)) : ℂ)) = 0 := by sorry
