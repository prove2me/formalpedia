-- Prove2me | Theorems.Thm_Formalism_DivisionValues_idxChange_locS_of_le
-- name    : Formalism.DivisionValues.idxChange_locS_of_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:06:35.168452+00:00
-- url     : https://prove2.me/theorems/8540cd57-491b-4756-97dc-1e7e118e8cff
-- title:
--   Division Values: idx Change loc S of le
-- statement:
--   The Division Values construction uses the idx Change loc S of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/IdxChange.lean#L229-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/IdxChange.lean#L229-L239

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

theorem Formalism.DivisionValues.idxChange_locS_of_le {S T : Submonoid R} (hTS : T ≤ S) {L M : Submodule R (Fin d → K)}
    (h : locS T L = locS T M) : locS S L = locS S M := by sorry
