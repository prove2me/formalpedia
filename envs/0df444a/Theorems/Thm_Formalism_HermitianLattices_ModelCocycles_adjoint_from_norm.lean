-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_ModelCocycles_adjoint_from_norm
-- name    : Formalism.HermitianLattices.ModelCocycles.adjoint_from_norm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:59:36.157678+00:00
-- url     : https://prove2.me/theorems/27fc9d8b-6cc2-4a4f-8179-12bbd3e41c24
-- title:
--   Model Cocycles: adjoint from norm
-- statement:
--   The Model Cocycles construction uses the adjoint from norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/TeichmullerUnitAllPrimes.lean#L8-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/TeichmullerUnitAllPrimes.lean#L8-L14

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_ModelCocycleExponent
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_TeichmullerUnitAllPrimes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ModelCocycles
open Finset Formalism.HermitianLattices.IntegralLatticeDensity

theorem Formalism.HermitianLattices.ModelCocycles.adjoint_from_norm : AdjointFromNorm := by sorry
