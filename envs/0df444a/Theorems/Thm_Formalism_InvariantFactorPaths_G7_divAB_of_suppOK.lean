-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_divAB_of_suppOK
-- name    : Formalism.InvariantFactorPaths.G7.divAB_of_suppOK
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:29:32.749297+00:00
-- url     : https://prove2.me/theorems/2d12218f-0ecb-4fbd-8fdb-237e432dc657
-- title:
--   G7: div AB of supp OK
-- statement:
--   The G7 construction uses the div AB of supp OK property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NormLiftLeOne.lean#L13-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NormLiftLeOne.lean#L13-L18

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

theorem Formalism.InvariantFactorPaths.G7.divAB_of_suppOK {K : Type} [Field K] {p : ℕ} {G : MvPowerSeries (Fin 2) K}
    (h : SuppOK p G) : DivAB G := by sorry
