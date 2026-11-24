-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_KernelCokernelKilling_coeff_gLog_single
-- name    : Formalism.L2.Th1.D.KernelCokernelKilling.coeff_gLog_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:49:24.640039+00:00
-- url     : https://prove2.me/theorems/c4e152a0-7b3a-4a9c-a095-8717e80a942d
-- title:
--   Kernel Cokernel Killing: coeff g Log single
-- statement:
--   The Kernel Cokernel Killing construction uses the coeff g Log single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/EqZeroOfPowEqOne.lean#L36-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/EqZeroOfPowEqOne.lean#L36-L66

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

theorem Formalism.L2.Th1.D.KernelCokernelKilling.coeff_gLog_single (hl : 2 ≤ l) (φ : ZMod d → τ) (s : ZMod d) (e : ℕ) :
    coeff (Finsupp.single (φ (s - 2 * (e : ZMod d))) ((l ^ 2) ^ e)) (gLog K l φ s) =
      ((l : K) ^ e)⁻¹ := by sorry
