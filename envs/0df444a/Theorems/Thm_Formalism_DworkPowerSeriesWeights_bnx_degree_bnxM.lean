-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_bnx_degree_bnxM
-- name    : Formalism.DworkPowerSeriesWeights.bnx_degree_bnxM
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:59:49.98558+00:00
-- url     : https://prove2.me/theorems/fbc1eb03-9757-4cca-b8a6-2dadfee920e5
-- title:
--   Dwork Power Series Weights: bnx degree bnx M
-- statement:
--   The Dwork Power Series Weights construction uses the bnx degree bnx M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SwappedParitySeriesBinomialForm.lean#L290-L295
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SwappedParitySeriesBinomialForm.lean#L290-L295

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_FormalGroupWitt_WeightInvariance
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SwappedParitySeriesBinomialForm
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
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open MvPowerSeries Formalism.IncomingBounds
variable {K : Type u} [Field K] {d : ℕ} [NeZero d]

theorem Formalism.DworkPowerSeriesWeights.bnx_degree_bnxM (n : ZMod d →₀ ℕ) (k : ZMod d → ℕ) (hk : ∀ s, k s ≤ n s) :
    (bnxM n k).degree = n.degree := by sorry
