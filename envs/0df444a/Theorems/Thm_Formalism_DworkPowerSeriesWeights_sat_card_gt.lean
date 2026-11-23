-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_sat_card_gt
-- name    : Formalism.DworkPowerSeriesWeights.sat_card_gt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:00:20.608476+00:00
-- url     : https://prove2.me/theorems/befa5f4b-face-4c88-b971-f12049ca7f40
-- title:
--   Dwork Power Series Weights: sat card gt
-- statement:
--   The Dwork Power Series Weights construction uses the sat card gt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SlopeBoundSaturation.lean#L83-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SlopeBoundSaturation.lean#L83-L90

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

theorem Formalism.DworkPowerSeriesWeights.sat_card_gt {n k C : ℕ} (sz : Fin k → ℕ) (p : Fin C → ℕ) (hsz : ∀ i, sz i ≤ n) (hp : ∀ c, p c ≤ n)
    (h : (shapeDeg sz : Fin n → ℕ) = shapeDeg p) (j : ℕ) :
    (Finset.univ.filter fun i => j < sz i).card = (Finset.univ.filter fun c => j < p c).card := by sorry
