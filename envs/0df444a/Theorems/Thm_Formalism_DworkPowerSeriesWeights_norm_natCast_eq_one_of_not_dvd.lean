-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_natCast_eq_one_of_not_dvd
-- name    : Formalism.DworkPowerSeriesWeights.norm_natCast_eq_one_of_not_dvd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:01:15.794697+00:00
-- url     : https://prove2.me/theorems/b32180bb-25c2-4ea2-bbdc-a8e0f1bae940
-- title:
--   Dwork Power Series Weights: norm nat Cast eq one of not dvd
-- statement:
--   The Dwork Power Series Weights construction uses the norm nat Cast eq one of not dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/NormNatCastEqPowPadicValNat.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/NormNatCastEqPowPadicValNat.lean#L17-L19

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ProdRangeEqFactorialMulProdIco
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormNatCastEqOneOfNotDvd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Theorems.Thm_GlobalTheory_NatCastUnitNorm_norm_natCast_eq_one_of_not_dvd

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
variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem Formalism.DworkPowerSeriesWeights.norm_natCast_eq_one_of_not_dvd {l m : ℕ} (hl : l.Prime) (hlt : ‖(l : K)‖ < 1)
    (hm : ¬ l ∣ m) : ‖(m : K)‖ = 1 := by sorry
