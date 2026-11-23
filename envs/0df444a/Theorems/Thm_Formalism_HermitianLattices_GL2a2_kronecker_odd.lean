-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_GL2a2_kronecker_odd
-- name    : Formalism.HermitianLattices.GL2a2.kronecker_odd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:20:50.017919+00:00
-- url     : https://prove2.me/theorems/591488a0-e8d9-4a67-bbf4-b24c0f3facd2
-- title:
--   GL2a2: kronecker odd
-- statement:
--   The GL2a2 construction uses the kronecker odd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/ShortIntervalImpliesProgressionsStatement.lean#L11-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/ShortIntervalImpliesProgressionsStatement.lean#L11-L19

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ShortIntervalImpliesProgressionsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology ArithmeticFunction
open scoped ENNReal
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GL2a2
open Formalism.HermitianLattices.GL2PrimeSums

theorem Formalism.HermitianLattices.GL2a2.kronecker_odd : KronOdd := by sorry
