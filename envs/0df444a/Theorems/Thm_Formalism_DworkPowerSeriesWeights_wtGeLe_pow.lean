-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_wtGeLe_pow
-- name    : Formalism.DworkPowerSeriesWeights.wtGeLe_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:08:11.676658+00:00
-- url     : https://prove2.me/theorems/d4742eef-d228-4378-bf41-03b14fe3ed9a
-- title:
--   Dwork Power Series Weights: wt Ge Le pow
-- statement:
--   The Dwork Power Series Weights construction uses the wt Ge Le pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/NormNatCastEqPowPadicValNat.lean#L49-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/NormNatCastEqPowPadicValNat.lean#L49-L60

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ProdRangeEqFactorialMulProdIco
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormNatCastEqOneOfNotDvd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
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
universe u v
open Formalism Formalism.DworkPowerSeriesWeights

theorem Formalism.DworkPowerSeriesWeights.wtGeLe_pow {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type v} {pi : ℝ}
    (h0 : 0 < pi) {r : ι → ℝ} {wt : ℝ} {κ : ι →₀ ℕ} {f : MvPowerSeries ι K}
    (hf : WtGeLe pi r wt κ f) (k : ℕ) : WtGeLe pi r (k * wt) κ (f ^ k) := by sorry
