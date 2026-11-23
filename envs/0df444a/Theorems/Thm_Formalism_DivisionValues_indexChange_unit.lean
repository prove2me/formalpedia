-- Prove2me | Theorems.Thm_Formalism_DivisionValues_indexChange_unit
-- name    : Formalism.DivisionValues.indexChange_unit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:31:47.662013+00:00
-- url     : https://prove2.me/theorems/48476322-6d25-425b-a1c8-0b3221ae2889
-- title:
--   Division Values: index Change unit
-- statement:
--   The Division Values construction uses the index Change unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/IdxChange.lean#L304-L334
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/IdxChange.lean#L304-L334

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

theorem Formalism.DivisionValues.indexChange_unit (v : HeightOneSpectrum R) (i : Fin d) {s : R} (hs : s ∉ v.asIdeal) :
    IdxChangeP v (idxChangeDg i (algebraMap R K s)) := by sorry
