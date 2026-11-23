-- Prove2me | Theorems.Thm_Formalism_DivisionValues_idxChange_locS_top
-- name    : Formalism.DivisionValues.idxChange_locS_top
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:31:47.308796+00:00
-- url     : https://prove2.me/theorems/80d1c030-3ec3-4913-87c1-387c10b55c7c
-- title:
--   Division Values: idx Change loc S top
-- statement:
--   The Division Values construction uses the idx Change loc S top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/IdxChange.lean#L171-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/IdxChange.lean#L171-L175

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDedekindDomain Formalism.HermitianLatticesTheory
open scoped Matrix nonZeroDivisors
noncomputable section
open Formalism Formalism.DivisionValues
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] {d : ℕ}

theorem Formalism.DivisionValues.idxChange_locS_top {e : Fin d → Fin d → K} (he : LinearIndependent K e) :
    locS (nonZeroDivisors R) (Submodule.span R (Set.range e)) = ⊤ := by sorry
