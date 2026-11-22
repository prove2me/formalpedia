-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_norm_lift_le_one
-- name    : Formalism.InvariantFactorPaths.G7.norm_lift_le_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:26:13.659833+00:00
-- url     : https://prove2.me/theorems/b9c87626-8cd5-429f-a85f-9869d9838d8d
-- title:
--   G7: norm lift le one
-- statement:
--   The G7 construction uses the norm lift le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NormLiftLeOne.lean#L20-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NormLiftLeOne.lean#L20-L30

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NormLiftLeOne
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
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)

theorem Formalism.InvariantFactorPaths.G7.norm_lift_le_one {K : Type} [NormedField K] [IsUltrametricDist K] {p : ℕ} {σ : K →+* K}
    (hU : UnrOK K p σ) {a : K} (ha : ‖a‖ ≤ 1) : ‖σ a‖ ≤ 1 := by sorry
