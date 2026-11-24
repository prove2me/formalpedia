-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_TailSumsHookFormulaTorsion_sum_log
-- name    : Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion.sum_log
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:02:51.361799+00:00
-- url     : https://prove2.me/theorems/e692a638-241d-404b-8d5f-99a475112255
-- title:
--   Tail Sums Hook Formula Torsion: sum log
-- statement:
--   The Tail Sums Hook Formula Torsion construction uses the sum log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/ExpNegLeDivPowFour.lean#L123-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/ExpNegLeDivPowFour.lean#L123-L152

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

theorem Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion.sum_log (M : ℕ) (hM : 2 ≤ M) (N : ℕ) (hN : M ≤ N) :
    ∑ n ∈ Ioc M N, 1 / Real.log (n : ℝ) ^ 2 / n ≤ 1 / Real.log (M : ℝ) := by sorry
