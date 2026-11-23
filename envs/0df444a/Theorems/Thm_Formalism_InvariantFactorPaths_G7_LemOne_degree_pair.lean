-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemOne_degree_pair
-- name    : Formalism.InvariantFactorPaths.G7.LemOne.degree_pair
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:54:24.29778+00:00
-- url     : https://prove2.me/theorems/3180ea19-5d44-4a52-80c7-e272cc5cf71f
-- title:
--   Lem One: degree pair
-- statement:
--   The Lem One construction uses the degree pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NotDvdChoosePowMul.lean#L150-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NotDvdChoosePowMul.lean#L150-L152

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NotDvdChoosePowMul
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
open Formalism.InvariantFactorPaths.G7.LemOne
variable {K : Type} [Field K]

theorem Formalism.InvariantFactorPaths.G7.LemOne.degree_pair (i j : ℕ) :
    (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) j).degree = i + j := by sorry
