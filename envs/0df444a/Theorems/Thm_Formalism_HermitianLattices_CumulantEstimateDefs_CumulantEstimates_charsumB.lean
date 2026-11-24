-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_CumulantEstimateDefs_CumulantEstimates_charsumB
-- name    : Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates.charsumB
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:39.832627+00:00
-- url     : https://prove2.me/theorems/9b6229df-e814-4eed-8f54-c1b8a787fa6a
-- title:
--   Cumulant Estimates: charsum B
-- statement:
--   The Cumulant Estimates construction uses the charsum B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/HilbertSchmidtHalfBound.lean#L355-L366
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/HilbertSchmidtHalfBound.lean#L355-L366

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

theorem Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates.charsumB (p : ℕ) [Fact p.Prime] (t : ZMod p) :
    ∑ c : (ZMod p)ˣ, (ZMod.stdAddChar ((c : ZMod p) * t) : ℂ) = if t = 0 then (p : ℂ) - 1 else -1 := by sorry
