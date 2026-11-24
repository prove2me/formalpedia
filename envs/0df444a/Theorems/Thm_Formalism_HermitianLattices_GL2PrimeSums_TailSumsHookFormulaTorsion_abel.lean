-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_TailSumsHookFormulaTorsion_abel
-- name    : Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion.abel
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:02:51.735332+00:00
-- url     : https://prove2.me/theorems/5aa4d71a-1e23-4192-9a5d-d4765aadc266
-- title:
--   Tail Sums Hook Formula Torsion: abel
-- statement:
--   The Tail Sums Hook Formula Torsion construction uses the abel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/ExpNegLeDivPowFour.lean#L18-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/ExpNegLeDivPowFour.lean#L18-L35

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

theorem Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion.abel (a : ℕ → ℂ) (M : ℕ) : ∀ N, M ≤ N →
    ∑ n ∈ Icc 1 N, a n / (n : ℂ) - ∑ n ∈ Icc 1 M, a n / (n : ℂ) =
      (∑ k ∈ Icc 1 N, a k) / ((N : ℂ) + 1) - (∑ k ∈ Icc 1 M, a k) / ((M : ℂ) + 1) +
        ∑ n ∈ Ioc M N, (∑ k ∈ Icc 1 n, a k) * (1 / (n : ℂ) - 1 / ((n : ℂ) + 1)) := by sorry
