-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_mean_le_one
-- name    : Formalism.HermitianLattices.GL2PrimeSums.gl2a5_mean_le_one
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:11.472403+00:00
-- url     : https://prove2.me/theorems/60b17522-7ec2-46b9-be18-770d615f7180
-- title:
--   GL2 Prime Sums: gl2a5 mean le one
-- statement:
--   The GL2 Prime Sums construction uses the gl2a5 mean le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean#L834-L842
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean#L834-L842

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SmallPrimeFactorSumBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GL2PrimeSums

theorem Formalism.HermitianLattices.GL2PrimeSums.gl2a5_mean_le_one (PPs : Finset ℕ) (a : ℤ) :
    |(∑ q ∈ PPs, (jacobiSym a q : ℝ)) / PPs.card| ≤ 1 := by sorry
