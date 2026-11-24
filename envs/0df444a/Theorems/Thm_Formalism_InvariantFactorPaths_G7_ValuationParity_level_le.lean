-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_ValuationParity_level_le
-- name    : Formalism.InvariantFactorPaths.G7.ValuationParity.level_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:28:44.095157+00:00
-- url     : https://prove2.me/theorems/29f8ace0-a623-4997-8b11-73608ed6d6ed
-- title:
--   Valuation Parity: level le
-- statement:
--   The Valuation Parity construction uses the level le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EntryAOneParity.lean#L127-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EntryAOneParity.lean#L127-L171

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

theorem Formalism.InvariantFactorPaths.G7.ValuationParity.level_le {ν r0 r1 E : ℕ} [NeZero ν] (p : ℕ) (e : TpV ν r1 → ℕ) (α : PhiI ν r0 r1 E → ℕ)
    (β : KapI ν r1 E →₀ ℕ)
    (hτ : ∀ τ, ∑ φ, α φ * dAof p φ τ + ∑ k, β k * dBof p k τ ≤ e τ)
    (c : PhiI ν r0 r1 E → ZMod (2 * ν) × ℕ)
    (hc : ∀ φ, p ^ (2 * (c φ).2 + 1) ≤ dAof p φ ((c φ).1, φ.2.2.2.2)) (s : ZMod (2 * ν)) (e' : ℕ) :
    p ^ (2 * e' + 1) * ((∑ φ, if c φ = (s, e') then α φ else 0) +
      ∑ k : KapI ν r1 E, if (k.1, k.2.1.val) = (s, e') then β k else 0) ≤ alN e s := by sorry
