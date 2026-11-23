-- Prove2me | Theorems.Thm_Formalism_REAL_polar_decomposition_eq
-- name    : Formalism.REAL.polar_decomposition_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:42:57.084046+00:00
-- url     : https://prove2.me/theorems/caf8c006-b5e8-4aa9-bad5-0ac914a44050
-- title:
--   REAL: polar decomposition eq
-- statement:
--   The REAL construction uses the polar decomposition eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/IndefiniteUnitaryPreservesForm.lean#L223-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/IndefiniteUnitaryPreservesForm.lean#L223-L225

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IndefiniteUnitaryPreservesForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder
noncomputable section
open Formalism Formalism.REAL
variable {n : ℕ}

theorem Formalism.REAL.polar_decomposition_eq {g : Matrix (Fin n) (Fin n) ℂ} :
    g = g * NormedSpace.exp (-polarLog g) * NormedSpace.exp (polarLog g) := by sorry
