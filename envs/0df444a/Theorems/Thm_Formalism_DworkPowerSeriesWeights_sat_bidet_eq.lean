-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_sat_bidet_eq
-- name    : Formalism.DworkPowerSeriesWeights.sat_bidet_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:01:24.757806+00:00
-- url     : https://prove2.me/theorems/1b205bd2-10dc-412a-b485-c267df0d04e2
-- title:
--   Dwork Power Series Weights: sat bidet eq
-- statement:
--   The Dwork Power Series Weights construction uses the sat bidet eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SlopeBoundSaturation.lean#L121-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SlopeBoundSaturation.lean#L121-L125

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementS
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SlopeBoundSaturation
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
open MvPolynomial
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.GradedWeylDivisibility

theorem Formalism.DworkPowerSeriesWeights.sat_bidet_eq (R : Type) [CommRing R] {r n k : ℕ} (sz : Fin k → ℕ) (hsz : ∀ i, sz i ≤ n)
    (I : ∀ i, Fin (sz i) → Fin r) : bideterminant R sz hsz I = ∏ i, satMinor R r n ⟨sz i, I i⟩ := by sorry
