-- Prove2me | Theorems.Thm_Formalism_DivisionValues_idxChange_unif
-- name    : Formalism.DivisionValues.idxChange_unif
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T22:36:09.552686+00:00
-- url     : https://prove2.me/theorems/4f526702-30a9-4e54-b902-a9310c97c6ef
-- title:
--   Division Values: idx Change unif
-- statement:
--   The Division Values construction uses the idx Change unif property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/IdxChange.lean#L73-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/IdxChange.lean#L73-L106

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
  [IsFractionRing R K]

theorem Formalism.DivisionValues.idxChange_unif (v : HeightOneSpectrum R) :
    ∃ ϖ : R, ϖ ∈ v.asIdeal ∧ ϖ ≠ 0 ∧
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ (algebraMap R K ϖ)) = 1 ∧
      ∃ t : R, t ∉ v.asIdeal ∧ ∀ x ∈ v.asIdeal, ∃ u : R, t * x = ϖ * u := by sorry
