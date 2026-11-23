-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_edgeW_swap_lt
-- name    : Formalism.DworkPowerSeriesWeights.edgeW_swap_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:57:47.512868+00:00
-- url     : https://prove2.me/theorems/771d9ddb-a38e-4cbe-bbef-f52c6f05cdfa
-- title:
--   Dwork Power Series Weights: edge W swap lt
-- statement:
--   The Dwork Power Series Weights construction uses the edge W swap lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffQuadSer.lean#L186-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffQuadSer.lean#L186-L208

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
variable {R : Type u} [CommRing R]

theorem Formalism.DworkPowerSeriesWeights.edgeW_swap_lt (w : Fin n → Fin n → R) {a b : Fin n} (hab : a < b) {τ : Equiv.Perm (Fin n)}
    (hτa : τ a = a) (hτb : τ b = b) : edgeW w (Equiv.swap a b * τ) = w a b * edgeW w τ := by sorry
