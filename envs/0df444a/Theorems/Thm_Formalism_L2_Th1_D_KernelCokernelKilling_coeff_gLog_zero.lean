-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_KernelCokernelKilling_coeff_gLog_zero
-- name    : Formalism.L2.Th1.D.KernelCokernelKilling.coeff_gLog_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:24:22.857818+00:00
-- url     : https://prove2.me/theorems/096aa42a-bbf7-4fd8-bad7-885506c565b1
-- title:
--   Kernel Cokernel Killing: coeff g Log zero
-- statement:
--   The Kernel Cokernel Killing construction uses the coeff g Log zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/EqZeroOfPowEqOne.lean#L68-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/EqZeroOfPowEqOne.lean#L68-L72

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
variable {K : Type} [Field K] {τ : Type} [DecidableEq τ] {l d : ℕ}

theorem Formalism.L2.Th1.D.KernelCokernelKilling.coeff_gLog_zero (φ : ZMod d → τ) (s : ZMod d) (n : τ →₀ ℕ)
    (h : ∀ e : ℕ, n ≠ Finsupp.single (φ (s - 2 * (e : ZMod d))) ((l ^ 2) ^ e)) :
    coeff n (gLog K l φ s) = 0 := by sorry
