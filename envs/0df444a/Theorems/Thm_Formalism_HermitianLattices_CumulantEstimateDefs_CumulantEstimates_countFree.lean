-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_CumulantEstimateDefs_CumulantEstimates_countFree
-- name    : Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates.countFree
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:10:22.236714+00:00
-- url     : https://prove2.me/theorems/213b415b-6390-4b94-8f9a-832758f3bddb
-- title:
--   Cumulant Estimates: count Free
-- statement:
--   The Cumulant Estimates construction uses the count Free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/HilbertSchmidtHalfBound.lean#L535-L547
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/HilbertSchmidtHalfBound.lean#L535-L547

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

theorem Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates.countFree (k rS r : ℕ) (hr : r = rS + (k + 1) + rS) :
    (univ.filter (fun ij : Fin r × Fin r => bb k rS ij.1.val < bb k rS ij.2.val)).card =
      rS * (2 * k + 1 + 2 * rS) := by sorry
