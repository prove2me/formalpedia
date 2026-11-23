-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_CumulantEstimateDefs_CumulantEstimates_normSymm
-- name    : Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates.normSymm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:10:26.053536+00:00
-- url     : https://prove2.me/theorems/df2e24b6-c115-42d0-ae33-e8758c9436bd
-- title:
--   Cumulant Estimates: norm Symm
-- statement:
--   The Cumulant Estimates construction uses the norm Symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/HilbertSchmidtHalfBound.lean#L139-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/HilbertSchmidtHalfBound.lean#L139-L141

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

theorem Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates.normSymm (N : ℕ) (X : Matrix (Fin N) (Fin N) ℂ) (hX : X.IsHermitian) (a b : Fin N) :
    ‖X a b‖ ^ 2 = ‖X b a‖ ^ 2 := by sorry
