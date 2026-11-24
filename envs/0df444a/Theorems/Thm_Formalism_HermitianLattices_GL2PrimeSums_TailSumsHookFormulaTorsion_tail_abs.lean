-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_TailSumsHookFormulaTorsion_tail_abs
-- name    : Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion.tail_abs
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:02:47.5748+00:00
-- url     : https://prove2.me/theorems/13a3004b-8776-4e97-9471-67ba199ee82f
-- title:
--   Tail Sums Hook Formula Torsion: tail abs
-- statement:
--   The Tail Sums Hook Formula Torsion construction uses the tail abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/ExpNegLeDivPowFour.lean#L37-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/ExpNegLeDivPowFour.lean#L37-L84

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ExpNegLeDivPowFour
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GL2PrimeSums Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion

theorem Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion.tail_abs (a : ℕ → ℂ) (S : ℂ)
    (hS : Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, a n / (n : ℂ)) atTop (𝓝 S))
    (M : ℕ) (hM : 1 ≤ M) (β : ℕ → ℝ) (B₀ B₁ : ℝ)
    (hβ : ∀ n, M ≤ n → ‖∑ k ∈ Icc 1 n, a k‖ ≤ n * β n)
    (h0 : ∀ n, M ≤ n → β n ≤ B₀)
    (h1 : ∀ N, M ≤ N → ∑ n ∈ Ioc M N, β n / n ≤ B₁) :
    ‖S - ∑ n ∈ Icc 1 M, a n / (n : ℂ)‖ ≤ 2 * B₀ + B₁ := by sorry
