-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_minFac_mem
-- name    : Formalism.HermitianLattices.GL2PrimeSums.gl2a5_minFac_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:28:53.183059+00:00
-- url     : https://prove2.me/theorems/7291f3d7-ad3d-4368-8f00-6da9bcf7bc4f
-- title:
--   GL2 Prime Sums: gl2a5 min Fac mem
-- statement:
--   The GL2 Prime Sums construction uses the gl2a5 min Fac mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean#L500-L503
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean#L500-L503

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

theorem Formalism.HermitianLattices.GL2PrimeSums.gl2a5_minFac_mem {N n : ℕ} (hn : n ∈ primesLeFinset N) : n.minFac ∈ Icc 1 N := by sorry
