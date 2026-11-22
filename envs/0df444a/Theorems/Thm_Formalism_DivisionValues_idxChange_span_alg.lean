-- Prove2me | Theorems.Thm_Formalism_DivisionValues_idxChange_span_alg
-- name    : Formalism.DivisionValues.idxChange_span_alg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:53:45.682809+00:00
-- url     : https://prove2.me/theorems/728f3cfd-fe4e-4572-8250-7ba543293bb8
-- title:
--   Division Values: idx Change span alg
-- statement:
--   The Division Values construction uses the idx Change span alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/IdxChange.lean#L48-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/IdxChange.lean#L48-L51

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

theorem Formalism.DivisionValues.idxChange_span_alg (a : R) :
    FractionalIdeal.spanSingleton R⁰ (algebraMap R K a) =
      ((Ideal.span {a} : Ideal R) : FractionalIdeal R⁰ K) := by sorry
