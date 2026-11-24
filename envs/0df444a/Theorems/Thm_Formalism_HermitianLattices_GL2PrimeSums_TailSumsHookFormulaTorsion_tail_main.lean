-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_TailSumsHookFormulaTorsion_tail_main
-- name    : Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion.tail_main
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:58:02.056542+00:00
-- url     : https://prove2.me/theorems/5924aafa-ff5e-4beb-a68f-a4bd0c4f0a37
-- title:
--   Tail Sums Hook Formula Torsion: tail main
-- statement:
--   The Tail Sums Hook Formula Torsion construction uses the tail main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/ExpNegLeDivPowFour.lean#L206-L288
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/ExpNegLeDivPowFour.lean#L206-L288

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

theorem Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion.tail_main (a : ℕ → ℂ) (S : ℂ)
    (hS : Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, a n / (n : ℂ)) atTop (𝓝 S))
    (M : ℕ) (hM : 3 ≤ M) (Q : ℝ) (hQ : 1 ≤ Q) (P E : ℝ) (hP : 0 ≤ P) (hE : 0 ≤ E)
    (hβ : ∀ n : ℕ, M ≤ n → ‖∑ k ∈ Icc 1 n, a k‖ ≤
      n * (P * ((n : ℝ) ^ (-((1 : ℝ) / 400)) * Real.log (n * Q) ^ 2) + E * (1 / Real.log (n : ℝ) ^ 2))) :
    ‖S - ∑ n ∈ Icc 1 M, a n / (n : ℂ)‖ ≤
      P * ((804 * Real.log (M * Q) ^ 2 + 5000000000) * (M : ℝ) ^ (-((1 : ℝ) / 400))) + 3 * E := by sorry
