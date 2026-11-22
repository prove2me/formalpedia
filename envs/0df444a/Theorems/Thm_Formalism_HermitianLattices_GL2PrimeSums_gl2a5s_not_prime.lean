-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5s_not_prime
-- name    : Formalism.HermitianLattices.GL2PrimeSums.gl2a5s_not_prime
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:44:50.608804+00:00
-- url     : https://prove2.me/theorems/bc8267bf-e445-4fea-a1af-711fd4dd626e
-- title:
--   GL2 Prime Sums: gl2a5s not prime
-- statement:
--   The GL2 Prime Sums construction uses the gl2a5s not prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean#L384-L391
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean#L384-L391

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

theorem Formalism.HermitianLattices.GL2PrimeSums.gl2a5s_not_prime (x : ℝ) (N : ℕ) {p : ℕ} (hp : ¬ p.Prime) : primeTermWeight x N p = 0 := by sorry
