-- Prove2me | Theorems.Thm_Formalism_DivisionValues_idxChange_cnt_mul
-- name    : Formalism.DivisionValues.idxChange_cnt_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T18:33:53.724751+00:00
-- url     : https://prove2.me/theorems/da166d3c-385f-46bd-9ba7-b6c515da2c8b
-- title:
--   Division Values: idx Change cnt mul
-- statement:
--   The Division Values construction uses the idx Change cnt mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/IdxChange.lean#L18-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/IdxChange.lean#L18-L24

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

theorem Formalism.DivisionValues.idxChange_cnt_mul (v : HeightOneSpectrum R) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ (x * y)) =
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ x) +
        FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ y) := by sorry
