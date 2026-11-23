-- Prove2me | Theorems.Thm_Formalism_DivisionValues_idxChange_cnt_ideal_zero
-- name    : Formalism.DivisionValues.idxChange_cnt_ideal_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:06:12.911662+00:00
-- url     : https://prove2.me/theorems/d8214dbc-1850-4b46-a713-5f4d0c40e073
-- title:
--   Division Values: idx Change cnt ideal zero
-- statement:
--   The Division Values construction uses the idx Change cnt ideal zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/IdxChange.lean#L31-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/IdxChange.lean#L31-L39

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

theorem Formalism.DivisionValues.idxChange_cnt_ideal_zero (v : HeightOneSpectrum R) (J : Ideal R) (hJ : J ≠ 0)
    (h : ¬ J ≤ v.asIdeal) : FractionalIdeal.count K v (J : FractionalIdeal R⁰ K) = 0 := by sorry
