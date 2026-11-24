-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_CumulantEstimateDefs_CumulantEstimates_factIneq
-- name    : Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates.factIneq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:49:22.781318+00:00
-- url     : https://prove2.me/theorems/d5a7afd5-a7ed-4fd1-8b82-af3c3f54f4a7
-- title:
--   Cumulant Estimates: fact Ineq
-- statement:
--   The Cumulant Estimates construction uses the fact Ineq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/HilbertSchmidtHalfBound.lean#L372-L384
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/HilbertSchmidtHalfBound.lean#L372-L384

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_QuadraticFormLowerBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HilbertSchmidtHalfBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.CumulantEstimateDefs Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates
open Finset
open scoped Nat

theorem Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates.factIneq (n : ℕ) : 6 ^ n * n ! ≤ (2 * n + 1)! := by sorry
