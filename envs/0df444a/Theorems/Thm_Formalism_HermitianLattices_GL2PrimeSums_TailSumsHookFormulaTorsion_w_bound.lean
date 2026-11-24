-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_TailSumsHookFormulaTorsion_w_bound
-- name    : Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion.w_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:58:20.52013+00:00
-- url     : https://prove2.me/theorems/3bb7808a-60a9-4beb-bd14-b8bf63be4856
-- title:
--   Tail Sums Hook Formula Torsion: w bound
-- statement:
--   The Tail Sums Hook Formula Torsion construction uses the w bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/ExpNegLeDivPowFour.lean#L160-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/ExpNegLeDivPowFour.lean#L160-L198

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

theorem Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion.w_bound (M n : ℕ) (hM : 1 ≤ M) (hn : M ≤ n) (Q : ℝ) (hQ : 1 ≤ Q) :
    (n : ℝ) ^ (-((1 : ℝ) / 400)) * Real.log (n * Q) ^ 2 ≤
      2 * Real.log (M * Q) ^ 2 * (n : ℝ) ^ (-((1 : ℝ) / 400)) +
        2 * 1600 ^ 2 * (M : ℝ) ^ (-((1 : ℝ) / 800)) * (n : ℝ) ^ (-((1 : ℝ) / 800)) := by sorry
