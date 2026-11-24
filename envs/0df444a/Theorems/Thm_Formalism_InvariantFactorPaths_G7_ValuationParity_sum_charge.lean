-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_ValuationParity_sum_charge
-- name    : Formalism.InvariantFactorPaths.G7.ValuationParity.sum_charge
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:34:09.229944+00:00
-- url     : https://prove2.me/theorems/ff9957cb-2891-4611-93bc-b94d116800d8
-- title:
--   Valuation Parity: sum charge
-- statement:
--   The Valuation Parity construction uses the sum charge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EntryAOneParity.lean#L96-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EntryAOneParity.lean#L96-L125

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EntryAOneParity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral jetPair mfact)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)
open Formalism.InvariantFactorPaths.G7.ValuationParity

theorem Formalism.InvariantFactorPaths.G7.ValuationParity.sum_charge {Φ S : Type} [Fintype Φ] [DecidableEq S] (TT : Finset S) (R : Finset ℕ)
    (c : Φ → S × ℕ) (w : Φ → ℕ) (h : ∀ φ, w φ ≠ 0 → (c φ).1 ∈ TT ∧ (c φ).2 ∈ R) :
    ∑ s ∈ TT, ∑ e ∈ R, ∑ φ, (if c φ = (s, e) then w φ else 0) = ∑ φ, w φ := by sorry
