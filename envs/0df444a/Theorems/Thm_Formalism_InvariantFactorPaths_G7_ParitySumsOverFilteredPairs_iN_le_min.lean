-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_ParitySumsOverFilteredPairs_iN_le_min
-- name    : Formalism.InvariantFactorPaths.G7.ParitySumsOverFilteredPairs.iN_le_min
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:55:19.667354+00:00
-- url     : https://prove2.me/theorems/ba37ec13-2c60-4b56-ac2d-c0a2a768d3e6
-- title:
--   Parity Sums Over Filtered Pairs: i N le min
-- statement:
--   The Parity Sums Over Filtered Pairs construction uses the i N le min property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EntryATwoAndB.lean#L151-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EntryATwoAndB.lean#L151-L162

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

theorem Formalism.InvariantFactorPaths.G7.ParitySumsOverFilteredPairs.iN_le_min (hC : HitsCapPos) {K : Type} [Field K] [NeZero ν] {C : ℕ} {p : ℕ} (hp : 0 < p)
    (ξ : ZMod (2 * ν) → Fin r0 → K) (α : PhiI ν r0 r1 E → ℕ) (β : KapI ν r1 E →₀ ℕ)
    (e : TpV ν r1 → ℕ) (l : Fin C → ℕ)
    (sf : Fin C → ZMod (2 * ν)) (T : ∀ c, Fin (l c) → Fin r0 → K) (I : ∀ c, Fin (l c) → Fin r1)
    (h3 : ∀ τ, ∑ φ, α φ * dAof p φ τ + ∑ k, β k * dBof p k τ ≤ e τ)
    (h4 : hasseDir (bBof p ξ) β (lowOp l sf T I) ≠ 0) (s : ZMod (2 * ν)) (e' : ℕ) :
    (iN β s e' : ℝ) ≤ min ((alN e s : ℝ) / (p : ℝ) ^ (2 * e' + 1))
      (capN sf (s + ((2 * e' + 1 : ℕ) : ZMod (2 * ν))) : ℝ) := by sorry
