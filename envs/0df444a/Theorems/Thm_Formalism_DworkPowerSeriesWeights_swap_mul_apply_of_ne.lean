-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_swap_mul_apply_of_ne
-- name    : Formalism.DworkPowerSeriesWeights.swap_mul_apply_of_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:15:55.893814+00:00
-- url     : https://prove2.me/theorems/9399714a-8378-48d4-8317-745c166d844a
-- title:
--   Dwork Power Series Weights: swap mul apply of ne
-- statement:
--   The Dwork Power Series Weights construction uses the swap mul apply of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffQuadSer.lean#L166-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffQuadSer.lean#L166-L171

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffQuadSer
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
variable {n : ℕ}

theorem Formalism.DworkPowerSeriesWeights.swap_mul_apply_of_ne {a b : Fin n} {τ : Equiv.Perm (Fin n)} (hτa : τ a = a) (hτb : τ b = b)
    {i : Fin n} (hia : i ≠ a) (hib : i ≠ b) : (Equiv.swap a b * τ) i = τ i := by sorry
