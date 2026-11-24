-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_geom
-- name    : Formalism.HermitianLattices.GL2PrimeSums.gl2a5_geom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:02:57.673793+00:00
-- url     : https://prove2.me/theorems/35f2f459-598c-4a95-97e2-33d4833581ab
-- title:
--   GL2 Prime Sums: gl2a5 geom
-- statement:
--   The GL2 Prime Sums construction uses the gl2a5 geom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean#L265-L272
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean#L265-L272

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

theorem Formalism.HermitianLattices.GL2PrimeSums.gl2a5_geom (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1 / 2) (a0 L : ℕ) :
    ∑ a ∈ Ioc a0 L, r ^ a ≤ 2 * r ^ (a0 + 1) := by sorry
