-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_ParitySumsOverFilteredPairs_pay_le
-- name    : Formalism.InvariantFactorPaths.G7.ParitySumsOverFilteredPairs.pay_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:55:23.714099+00:00
-- url     : https://prove2.me/theorems/f92ace19-7e46-402e-a85b-8b98df492fb9
-- title:
--   Parity Sums Over Filtered Pairs: pay le
-- statement:
--   The Parity Sums Over Filtered Pairs construction uses the pay le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EntryATwoAndB.lean#L74-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EntryATwoAndB.lean#L74-L105

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_GrowthSums_StatementG
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EntryATwoAndB
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
open Formalism.InvariantFactorPaths.G7.ParitySumsOverFilteredPairs
variable {ν r0 r1 E : ℕ}

theorem Formalism.InvariantFactorPaths.G7.ParitySumsOverFilteredPairs.pay_le [NeZero ν] {p : ℕ} (hp : 0 < p) (α : PhiI ν r0 r1 E → ℕ) (β : KapI ν r1 E →₀ ℕ)
    (e : TpV ν r1 → ℕ)
    (h3 : ∀ τ, ∑ φ, α φ * dAof p φ τ + ∑ k, β k * dBof p k τ ≤ e τ) (P : Finset (TpV ν r1))
    (hP : ∀ φ, α φ ≠ 0 → (pairFirst φ, φ.2.2.2.2) ∈ P ∨ (pairSecond φ, φ.2.2.2.2) ∈ P) :
    ∑ φ, α φ + ∑ k ∈ univ.filter (fun k : KapI ν r1 E => (k.1, k.2.2) ∈ P), β k ≤
      ∑ τ ∈ P, e τ := by sorry
