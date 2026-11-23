-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_sat_prod_fibers
-- name    : Formalism.DworkPowerSeriesWeights.sat_prod_fibers
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:00:28.854239+00:00
-- url     : https://prove2.me/theorems/616c6c2c-cf34-4906-806b-b995374a9c9c
-- title:
--   Dwork Power Series Weights: sat prod fibers
-- statement:
--   The Dwork Power Series Weights construction uses the sat prod fibers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SlopeBoundSaturation.lean#L131-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SlopeBoundSaturation.lean#L131-L140

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

theorem Formalism.DworkPowerSeriesWeights.sat_prod_fibers {A : Type} [CommMonoid A] {n k : ℕ} (sz : Fin k → ℕ) (hsz : ∀ i, sz i ≤ n) (G : Fin k → A)
    (hG : ∀ i, sz i = 0 → G i = 1) :
    ∏ i, G i = ∏ j ∈ Finset.range n, ∏ i : {i // sz i = j + 1}, G i.1 := by sorry
