-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_KernelCokernelKilling_iter_sub_two
-- name    : Formalism.L2.Th1.D.KernelCokernelKilling.iter_sub_two
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:24:37.382007+00:00
-- url     : https://prove2.me/theorems/9acc07f4-728e-43b1-8abb-308ac5ce164c
-- title:
--   Kernel Cokernel Killing: iter sub two
-- statement:
--   The Kernel Cokernel Killing construction uses the iter sub two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/EqZeroOfPowEqOne.lean#L192-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/EqZeroOfPowEqOne.lean#L192-L199

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_EqZeroOfPowEqOne
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_frobVar_eq_expand

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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral letterLog entLog)
open Formalism.InvariantFactorPaths.G7 (frobVar frobVar_eq_expand UnrOK)
open Formalism.L2.Th1.D.KernelCokernelKilling
open MvPowerSeries
variable {K : Type} [NormedField K] {τ : Type}

theorem Formalism.L2.Th1.D.KernelCokernelKilling.iter_sub_two {α : Type} {d : ℕ} [NeZero d] (f : α → α) {c : α} (hc : f^[d] c = c)
    (t : ZMod d) : f (f (f^[(t - 2).val] c)) = f^[t.val] c := by sorry
