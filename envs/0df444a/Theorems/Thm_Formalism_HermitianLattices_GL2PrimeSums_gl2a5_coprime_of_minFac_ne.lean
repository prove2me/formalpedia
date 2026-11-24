-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_coprime_of_minFac_ne
-- name    : Formalism.HermitianLattices.GL2PrimeSums.gl2a5_coprime_of_minFac_ne
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:10.067365+00:00
-- url     : https://prove2.me/theorems/3543a79a-f037-4c96-b7f4-c05d61bdffbc
-- title:
--   GL2 Prime Sums: gl2a5 coprime of min Fac ne
-- statement:
--   The GL2 Prime Sums construction uses the gl2a5 coprime of min Fac ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean#L75-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean#L75-L80

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

theorem Formalism.HermitianLattices.GL2PrimeSums.gl2a5_coprime_of_minFac_ne {n n' : ℕ} (hn : IsPrimePow n) (hn' : IsPrimePow n')
    (h : n.minFac ≠ n'.minFac) : Nat.Coprime n n' := by sorry
