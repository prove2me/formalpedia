-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_CumulantEstimateDefs_CumulantEstimates_natIneq
-- name    : Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates.natIneq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:49:18.825054+00:00
-- url     : https://prove2.me/theorems/ca8c93cc-b3bf-4fb5-8d6b-106aae211f19
-- title:
--   Cumulant Estimates: nat Ineq
-- statement:
--   The Cumulant Estimates construction uses the nat Ineq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/HilbertSchmidtHalfBound.lean#L229-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/HilbertSchmidtHalfBound.lean#L229-L237

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
open Finset MeasureTheory
open scoped ComplexOrder

theorem Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates.natIneq (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (h : ¬ (p = 1 ∧ q = 1)) :
    p + q + 1 ≤ 2 * p * q := by sorry
