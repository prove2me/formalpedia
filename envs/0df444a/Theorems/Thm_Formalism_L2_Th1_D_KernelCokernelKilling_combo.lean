-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_KernelCokernelKilling_combo
-- name    : Formalism.L2.Th1.D.KernelCokernelKilling.combo
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:49:25.367156+00:00
-- url     : https://prove2.me/theorems/1d62f73c-52b2-4730-9662-0caa2cb18803
-- title:
--   Kernel Cokernel Killing: combo
-- statement:
--   The Kernel Cokernel Killing construction uses the combo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/EqZeroOfPowEqOne.lean#L207-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/EqZeroOfPowEqOne.lean#L207-L252

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

theorem Formalism.L2.Th1.D.KernelCokernelKilling.combo [IsUltrametricDist K] {l d : ℕ} [NeZero d] (hl : l ≠ 0) (σ : K →+* K)
    (hσ : ∀ a : K, ‖a‖ ≤ 1 → ‖σ a‖ ≤ 1) (hd : Even d) (L : ZMod d → MvPowerSeries τ K)
    (hL : ShiftType l σ L) {c : K} (hc : ‖c‖ ≤ 1) (hcd : σ^[d] c = c)
    (P : ℕ → Prop) [DecidablePred P] :
    IP l σ (∑ s : ZMod d, if P (s.val % 2) then C (σ^[s.val] c) * L s else 0) := by sorry
