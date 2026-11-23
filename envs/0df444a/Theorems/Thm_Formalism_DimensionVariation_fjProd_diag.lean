-- Prove2me | Theorems.Thm_Formalism_DimensionVariation_fjProd_diag
-- name    : Formalism.DimensionVariation.fjProd_diag
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:11:20.27682+00:00
-- url     : https://prove2.me/theorems/99ae377f-0280-46d4-964a-e3b2ab9ae4af
-- title:
--   Dimension Variation: fj Prod diag
-- statement:
--   The Dimension Variation construction uses the fj Prod diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaSupremumBounds/GaussianShiftBounds/FockJet.lean#L164-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaSupremumBounds/GaussianShiftBounds/FockJet.lean#L164-L173

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

theorem Formalism.DimensionVariation.fjProd_diag {κ : Type} [Fintype κ] (e : κ → ℕ) :
    ∫ u : κ → ℂ, mono u e * mono (cj u) e * (Real.exp (-(nsq u)) : ℂ) =
      (π : ℂ) ^ Fintype.card κ * (mfact e : ℂ) := by sorry
