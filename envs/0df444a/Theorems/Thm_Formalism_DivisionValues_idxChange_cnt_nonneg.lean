-- Prove2me | Theorems.Thm_Formalism_DivisionValues_idxChange_cnt_nonneg
-- name    : Formalism.DivisionValues.idxChange_cnt_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:31:21.684029+00:00
-- url     : https://prove2.me/theorems/97f092df-d931-4734-8ea6-62d09efb0f32
-- title:
--   Division Values: idx Change cnt nonneg
-- statement:
--   The Division Values construction uses the idx Change cnt nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/IdxChange.lean#L68-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/IdxChange.lean#L68-L71

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

theorem Formalism.DivisionValues.idxChange_cnt_nonneg (v : HeightOneSpectrum R) (a : R) :
    0 ≤ FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ (algebraMap R K a)) := by sorry
