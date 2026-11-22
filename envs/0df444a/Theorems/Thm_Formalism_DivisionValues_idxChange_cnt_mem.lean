-- Prove2me | Theorems.Thm_Formalism_DivisionValues_idxChange_cnt_mem
-- name    : Formalism.DivisionValues.idxChange_cnt_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:50:50.615389+00:00
-- url     : https://prove2.me/theorems/fec08ba1-0df5-4be5-936e-728b826e8e4c
-- title:
--   Division Values: idx Change cnt mem
-- statement:
--   The Division Values construction uses the idx Change cnt mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/IdxChange.lean#L61-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/IdxChange.lean#L61-L66

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

theorem Formalism.DivisionValues.idxChange_cnt_mem (v : HeightOneSpectrum R) {a : R} (ha : a ≠ 0) (hp : a ∈ v.asIdeal) :
    1 ≤ FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ (algebraMap R K a)) := by sorry
