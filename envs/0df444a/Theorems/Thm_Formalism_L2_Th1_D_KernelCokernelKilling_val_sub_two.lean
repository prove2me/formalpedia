-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_KernelCokernelKilling_val_sub_two
-- name    : Formalism.L2.Th1.D.KernelCokernelKilling.val_sub_two
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:24:20.941802+00:00
-- url     : https://prove2.me/theorems/0ffeae73-8867-4827-80f1-ef53b25a5ced
-- title:
--   Kernel Cokernel Killing: val sub two
-- statement:
--   The Kernel Cokernel Killing construction uses the val sub two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/EqZeroOfPowEqOne.lean#L171-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/EqZeroOfPowEqOne.lean#L171-L183

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

theorem Formalism.L2.Th1.D.KernelCokernelKilling.val_sub_two {d : ℕ} [NeZero d] (t : ZMod d) :
    ∃ k : ℕ, (t - 2).val + 2 = t.val + d * k := by sorry
