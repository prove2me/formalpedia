-- Prove2me | Theorems.Thm_Formalism_DivisionValues_indexChange_integral
-- name    : Formalism.DivisionValues.indexChange_integral
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:31:45.29608+00:00
-- url     : https://prove2.me/theorems/a21a5ab9-0e8f-4951-91a6-039fa0f56f43
-- title:
--   Division Values: index Change integral
-- statement:
--   The Division Values construction uses the index Change integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/IdxChange.lean#L468-L513
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/IdxChange.lean#L468-L513

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

theorem Formalism.DivisionValues.indexChange_integral (v : HeightOneSpectrum R) (i : Fin d) :
    ∀ n : ℕ, ∀ a : R, a ≠ 0 →
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ (algebraMap R K a)) = n →
      IdxChangeP v (idxChangeDg i (algebraMap R K a)) := by sorry
