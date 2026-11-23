-- Prove2me | Theorems.Thm_Formalism_DivisionValues_indexChange_uniformizer
-- name    : Formalism.DivisionValues.indexChange_uniformizer
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:31:40.154892+00:00
-- url     : https://prove2.me/theorems/d08bf4c0-c55b-49af-8f72-f25b0e86eeea
-- title:
--   Division Values: index Change uniformizer
-- statement:
--   The Division Values construction uses the index Change uniformizer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/IdxChange.lean#L343-L459
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/IdxChange.lean#L343-L459

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

theorem Formalism.DivisionValues.indexChange_uniformizer (v : HeightOneSpectrum R) (i : Fin d) {ϖ t : R}
    (hcnt : FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ (algebraMap R K ϖ)) = 1)
    (htp : t ∉ v.asIdeal) (ht : ∀ x ∈ v.asIdeal, ∃ u : R, t * x = ϖ * u) :
    IdxChangeP v (idxChangeDg i (algebraMap R K ϖ)) := by sorry
