-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemOne_coeff_rem
-- name    : Formalism.InvariantFactorPaths.G7.LemOne.coeff_rem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:54:17.062258+00:00
-- url     : https://prove2.me/theorems/3d228eac-7e98-40a1-8985-fba4c472296c
-- title:
--   Lem One: coeff rem
-- statement:
--   The Lem One construction uses the coeff rem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NotDvdChoosePowMul.lean#L383-L387
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NotDvdChoosePowMul.lean#L383-L387

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
variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem Formalism.InvariantFactorPaths.G7.LemOne.coeff_rem (p : ℕ) (f : PowerSeries K) (a b : K) (n : ℕ) :
    PowerSeries.coeff n (rem p f a b) = PowerSeries.coeff n f - a * PowerSeries.coeff n (g0F K p) -
      b * PowerSeries.coeff n (lgF K p) := by sorry
