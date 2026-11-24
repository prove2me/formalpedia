-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_CumulantEstimateDefs_hilbert_schmidt_half_bound
-- name    : Formalism.HermitianLattices.CumulantEstimateDefs.hilbert_schmidt_half_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:49:22.825451+00:00
-- url     : https://prove2.me/theorems/cb7f996d-9743-44c1-8075-ab182740fb32
-- title:
--   Cumulant Estimate Defs: hilbert schmidt half bound
-- statement:
--   The Cumulant Estimate Defs construction uses the hilbert schmidt half bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/HilbertSchmidtHalfBound.lean#L586-L586
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/HilbertSchmidtHalfBound.lean#L586-L586

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.CumulantEstimateDefs

theorem Formalism.HermitianLattices.CumulantEstimateDefs.hilbert_schmidt_half_bound : HilbertSchmidtHalfBound := by sorry
