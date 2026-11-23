-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_sat_coeff_prod_rename
-- name    : Formalism.DworkPowerSeriesWeights.sat_coeff_prod_rename
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:00:33.420986+00:00
-- url     : https://prove2.me/theorems/cb1237f7-f99e-4762-bef5-eb22a0b1b53b
-- title:
--   Dwork Power Series Weights: sat coeff prod rename
-- statement:
--   The Dwork Power Series Weights construction uses the sat coeff prod rename property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SlopeBoundSaturation.lean#L51-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SlopeBoundSaturation.lean#L51-L81

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

theorem Formalism.DworkPowerSeriesWeights.sat_coeff_prod_rename {R S τ σ : Type} [CommSemiring R] [Fintype S] [DecidableEq S] (e : S → τ → σ)
    (he : ∀ s t v w, e s v = e t w → s = t ∧ v = w) (f : S → MvPolynomial τ R) (m : S → τ →₀ ℕ) :
    coeff (∑ s, (m s).mapDomain (e s)) (∏ s, rename (e s) (f s)) = ∏ s, coeff (m s) (f s) := by sorry
