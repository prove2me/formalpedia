-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_CumulantEstimateDefs_CumulantEstimates_halfSum
-- name    : Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates.halfSum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:10:15.402569+00:00
-- url     : https://prove2.me/theorems/0336c3ec-7920-48bc-bcc8-1ac840c39893
-- title:
--   Cumulant Estimates: half Sum
-- statement:
--   The Cumulant Estimates construction uses the half Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/HilbertSchmidtHalfBound.lean#L109-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/HilbertSchmidtHalfBound.lean#L109-L137

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

theorem Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates.halfSum (N : ℕ) (sg : Fin N → Bool) (f : Fin N → Fin N → ℝ)
    (hs : ∀ a b, f a b = f b a) (h0 : ∀ a b, sg a = sg b → f a b = 0) :
    ∑ a, ∑ b, f a b = 2 * ∑ a, ∑ b ∈ univ.filter (fun b => b < a ∧ sg a ≠ sg b), f a b := by sorry
