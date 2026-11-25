-- Prove2me | Theorems.Thm_Formalism_L2_S_Pv_SchurTens_limit_memLp_and_integral_eq
-- name    : Formalism.L2.S.Pv.SchurTens.limit_memLp_and_integral_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T06:13:45.606637+00:00
-- url     : https://prove2.me/theorems/8f94b561-a26f-4e79-81a7-588c568304ae
-- title:
--   Schur Tens: limit mem Lp and integral eq
-- statement:
--   The Schur Tens construction uses the limit mem Lp and integral eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/LimitMemLpAndIntegralEq.lean#L99-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/LimitMemLpAndIntegralEq.lean#L99-L154

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_LimitMemLpAndIntegralEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.SchurTens
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem Formalism.L2.S.Pv.SchurTens.limit_memLp_and_integral_eq (f : ℕ → X → ℂ) (F g : X → ℂ) (hf2 : ∀ n, MemLp (f n) 2 μ) (hFm : AEStronglyMeasurable F μ)
    (hg : MemLp g 2 μ) (hpt : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (F x)))
    (hC : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ n ≥ N, ∀ m ≥ N, ∫⁻ x, ‖f m x - f n x‖ₑ ^ 2 ∂μ ≤ ε)
    {L : ℂ} (hL : Tendsto (fun n => ∫ x, f n x * conj (g x) ∂μ) atTop (𝓝 L)) :
    MemLp F 2 μ ∧ Integrable (fun x => F x * conj (g x)) μ ∧ ∫ x, F x * conj (g x) ∂μ = L := by sorry
