-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_swap_mul_sq
-- name    : Formalism.DworkPowerSeriesWeights.swap_mul_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:08:15.401287+00:00
-- url     : https://prove2.me/theorems/54536c99-67aa-4051-85de-d8c772d4e69d
-- title:
--   Dwork Power Series Weights: swap mul sq
-- statement:
--   The Dwork Power Series Weights construction uses the swap mul sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffQuadSer.lean#L230-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffQuadSer.lean#L230-L238

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

theorem Formalism.DworkPowerSeriesWeights.swap_mul_sq {a b : Fin n} {τ : Equiv.Perm (Fin n)} (hτ : τ * τ = 1)
    (h : Equiv.swap (τ a) (τ b) = Equiv.swap a b) :
    (Equiv.swap a b * τ) * (Equiv.swap a b * τ) = 1 := by sorry
