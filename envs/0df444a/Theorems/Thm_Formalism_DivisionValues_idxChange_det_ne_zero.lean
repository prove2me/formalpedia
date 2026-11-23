-- Prove2me | Theorems.Thm_Formalism_DivisionValues_idxChange_det_ne_zero
-- name    : Formalism.DivisionValues.idxChange_det_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:31:28.558545+00:00
-- url     : https://prove2.me/theorems/e55f4fb2-1cae-4d69-85e3-216e603118e7
-- title:
--   Division Values: idx Change det ne zero
-- statement:
--   The Division Values construction uses the idx Change det ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/IdxChange.lean#L152-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/IdxChange.lean#L152-L161

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

theorem Formalism.DivisionValues.idxChange_det_ne_zero {e : Fin d → Fin d → K} {γ : Matrix (Fin d) (Fin d) K}
    (he : LinearIndependent K (idxChangeAct e γ)) : γ.det ≠ 0 := by sorry
