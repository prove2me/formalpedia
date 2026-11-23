-- Prove2me | Theorems.Thm_Formalism_DivisionValues_indexChange_of_det_ne_zero
-- name    : Formalism.DivisionValues.indexChange_of_det_ne_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:45:09.030049+00:00
-- url     : https://prove2.me/theorems/6b3ba629-83c6-4655-859b-d67eeaf99654
-- title:
--   Division Values: index Change of det ne zero
-- statement:
--   The Division Values construction uses the index Change of det ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/IdxChange.lean#L640-L647
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/IdxChange.lean#L640-L647

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

theorem Formalism.DivisionValues.indexChange_of_det_ne_zero (v : HeightOneSpectrum R) (γ : Matrix (Fin d) (Fin d) K) (hγ : γ.det ≠ 0) :
    IdxChangeP v γ := by sorry
