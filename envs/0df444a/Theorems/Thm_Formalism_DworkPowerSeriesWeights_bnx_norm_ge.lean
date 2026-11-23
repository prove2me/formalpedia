-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_bnx_norm_ge
-- name    : Formalism.DworkPowerSeriesWeights.bnx_norm_ge
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:56:15.708434+00:00
-- url     : https://prove2.me/theorems/a2bf21b2-4504-4935-9940-f3fb2837ce48
-- title:
--   Dwork Power Series Weights: bnx norm ge
-- statement:
--   The Dwork Power Series Weights construction uses the bnx norm ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SwappedParitySeriesBinomialForm.lean#L417-L427
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SwappedParitySeriesBinomialForm.lean#L417-L427

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
variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem Formalism.DworkPowerSeriesWeights.bnx_norm_ge {l : ℕ} (hl : l.Prime) (hl1 : ‖(l : K)‖ < 1) (B : ℕ) (hB0 : B ≠ 0)
    (hB : ¬ l ^ 2 ∣ B) : ‖(l : K)‖ ≤ ‖(B : K)‖ := by sorry
