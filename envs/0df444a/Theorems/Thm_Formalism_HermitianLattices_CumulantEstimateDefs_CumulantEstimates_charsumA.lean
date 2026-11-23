-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_CumulantEstimateDefs_CumulantEstimates_charsumA
-- name    : Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates.charsumA
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:10:37.446281+00:00
-- url     : https://prove2.me/theorems/2f1f6af6-941a-42a9-be7f-deaf85bc82b9
-- title:
--   Cumulant Estimates: charsum A
-- statement:
--   The Cumulant Estimates construction uses the charsum A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/HilbertSchmidtHalfBound.lean#L350-L353
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/HilbertSchmidtHalfBound.lean#L350-L353

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

theorem Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates.charsumA (n : ℕ) [NeZero n] (t : ZMod n) :
    ∑ b : ZMod n, (ZMod.stdAddChar (b * t) : ℂ) = if t = 0 then (n : ℂ) else 0 := by sorry
