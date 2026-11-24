-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_ParitySumsOverFilteredPairs_iN_le_cap
-- name    : Formalism.InvariantFactorPaths.G7.ParitySumsOverFilteredPairs.iN_le_cap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:32:50.471453+00:00
-- url     : https://prove2.me/theorems/3b532076-933f-4ece-88ef-39e1a4fa2288
-- title:
--   Parity Sums Over Filtered Pairs: i N le cap
-- statement:
--   The Parity Sums Over Filtered Pairs construction uses the i N le cap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EntryATwoAndB.lean#L125-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EntryATwoAndB.lean#L125-L149

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

theorem Formalism.InvariantFactorPaths.G7.ParitySumsOverFilteredPairs.iN_le_cap (hC : HitsCapPos) {K : Type} [Field K] [NeZero ν] {C : ℕ} (p : ℕ)
    (ξ : ZMod (2 * ν) → Fin r0 → K) (β : KapI ν r1 E →₀ ℕ) (l : Fin C → ℕ)
    (sf : Fin C → ZMod (2 * ν)) (T : ∀ c, Fin (l c) → Fin r0 → K) (I : ∀ c, Fin (l c) → Fin r1)
    (h4 : hasseDir (bBof p ξ) β (lowOp l sf T I) ≠ 0) (s : ZMod (2 * ν)) (e' : ℕ) :
    iN β s e' ≤ capN sf (s + ((2 * e' + 1 : ℕ) : ZMod (2 * ν))) := by sorry
