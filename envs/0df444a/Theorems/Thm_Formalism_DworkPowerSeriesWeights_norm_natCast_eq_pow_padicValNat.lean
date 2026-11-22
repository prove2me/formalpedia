-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_natCast_eq_pow_padicValNat
-- name    : Formalism.DworkPowerSeriesWeights.norm_natCast_eq_pow_padicValNat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:09:31.926638+00:00
-- url     : https://prove2.me/theorems/11da2f77-2984-49d0-8fe0-f2bdb0beaa93
-- title:
--   Dwork Power Series Weights: norm nat Cast eq pow padic Val Nat
-- statement:
--   The Dwork Power Series Weights construction uses the norm nat Cast eq pow padic Val Nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/NormNatCastEqPowPadicValNat.lean#L21-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/NormNatCastEqPowPadicValNat.lean#L21-L28

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
variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem Formalism.DworkPowerSeriesWeights.norm_natCast_eq_pow_padicValNat {l n : ℕ} (hl : l.Prime) (hlt : ‖(l : K)‖ < 1)
    (hn : n ≠ 0) : ‖(n : K)‖ = ‖(l : K)‖ ^ padicValNat l n := by sorry
