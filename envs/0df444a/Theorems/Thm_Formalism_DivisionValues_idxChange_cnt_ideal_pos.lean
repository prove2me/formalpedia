-- Prove2me | Theorems.Thm_Formalism_DivisionValues_idxChange_cnt_ideal_pos
-- name    : Formalism.DivisionValues.idxChange_cnt_ideal_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:30:58.382912+00:00
-- url     : https://prove2.me/theorems/c6bb3e26-d2ed-4880-9df9-0aab9a0336d8
-- title:
--   Division Values: idx Change cnt ideal pos
-- statement:
--   The Division Values construction uses the idx Change cnt ideal pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/IdxChange.lean#L41-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/IdxChange.lean#L41-L46

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

theorem Formalism.DivisionValues.idxChange_cnt_ideal_pos (v : HeightOneSpectrum R) (J : Ideal R) (hJ : J ≠ 0)
    (h : J ≤ v.asIdeal) : 1 ≤ FractionalIdeal.count K v (J : FractionalIdeal R⁰ K) := by sorry
