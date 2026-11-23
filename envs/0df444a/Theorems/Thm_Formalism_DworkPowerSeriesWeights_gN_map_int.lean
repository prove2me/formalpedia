-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_gN_map_int
-- name    : Formalism.DworkPowerSeriesWeights.gN_map_int
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:58:29.514009+00:00
-- url     : https://prove2.me/theorems/4eb20042-2d39-40b2-8489-65c9b0675eb4
-- title:
--   Dwork Power Series Weights: g N map int
-- statement:
--   The Dwork Power Series Weights construction uses the g N map int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/GField.lean#L201-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/GField.lean#L201-L215

import Definitions.Def_Formalism_GaussJetBounds_StatementM
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_GField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators NNReal
open Formalism Formalism.DworkPowerSeriesWeights
open MvPolynomial

theorem Formalism.DworkPowerSeriesWeights.gN_map_int (l : ℕ) [Fact l.Prime] {σ : Type} (P : MvPolynomial σ ℤ)
    (hP : MvPolynomial.map (Int.castRingHom (ZMod l)) P ≠ 0) :
    gN (MvPolynomial.map (Int.castRingHom ℂ_[l]) P) = 1 := by sorry
