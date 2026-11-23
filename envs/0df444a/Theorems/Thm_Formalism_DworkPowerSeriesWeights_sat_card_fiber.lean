-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_sat_card_fiber
-- name    : Formalism.DworkPowerSeriesWeights.sat_card_fiber
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:01:02.223327+00:00
-- url     : https://prove2.me/theorems/614b51af-71bf-45b8-af89-65ba2b666e95
-- title:
--   Dwork Power Series Weights: sat card fiber
-- statement:
--   The Dwork Power Series Weights construction uses the sat card fiber property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SlopeBoundSaturation.lean#L100-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SlopeBoundSaturation.lean#L100-L108

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

theorem Formalism.DworkPowerSeriesWeights.sat_card_fiber {n k C : ℕ} (sz : Fin k → ℕ) (p : Fin C → ℕ) (hsz : ∀ i, sz i ≤ n) (hp : ∀ c, p c ≤ n)
    (h : (shapeDeg sz : Fin n → ℕ) = shapeDeg p) (j : ℕ) :
    Fintype.card {c // p c = j + 1} = Fintype.card {i // sz i = j + 1} := by sorry
