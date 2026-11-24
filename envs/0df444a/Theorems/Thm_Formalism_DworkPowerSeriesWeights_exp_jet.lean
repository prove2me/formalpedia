-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_exp_jet
-- name    : Formalism.DworkPowerSeriesWeights.exp_jet
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:44:22.323876+00:00
-- url     : https://prove2.me/theorems/28285c23-ebff-4694-943c-d4c8ff23b08d
-- title:
--   Dwork Power Series Weights: exp jet
-- statement:
--   The Dwork Power Series Weights construction uses the exp jet property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/MfactEqProdUniv.lean#L64-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/MfactEqProdUniv.lean#L64-L116

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_MfactEqProdUniv
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
variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CharZero K]

theorem Formalism.DworkPowerSeriesWeights.exp_jet (r : ℝ) (hr : 1 ≤ r) (ι : Type) [Fintype ι] (S : K) (u : ι → K) (hS : ‖S‖ ≤ r)
    (hu : ∀ i, ‖u i‖ ≤ 1) (κ : (Bool × ι) →₀ ℕ) :
    ‖((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ
        (mvExp ((-S) • ∑ i, MvPowerSeries.C (u i) * MvPowerSeries.X (false, i) *
          MvPowerSeries.X (true, i)))‖ ≤ r ^ (∑ i, min (κ (false, i)) (κ (true, i))) := by sorry
