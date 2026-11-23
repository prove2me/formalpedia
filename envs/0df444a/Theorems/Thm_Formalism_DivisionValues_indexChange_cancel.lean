-- Prove2me | Theorems.Thm_Formalism_DivisionValues_indexChange_cancel
-- name    : Formalism.DivisionValues.indexChange_cancel
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T00:07:06.971895+00:00
-- url     : https://prove2.me/theorems/84c6023d-f1d7-44e6-9e36-05341f14270f
-- title:
--   Division Values: index Change cancel
-- statement:
--   The Division Values construction uses the index Change cancel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/IdxChange.lean#L291-L302
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/IdxChange.lean#L291-L302

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

theorem Formalism.DivisionValues.indexChange_cancel (v : HeightOneSpectrum R) (i : Fin d) {x y : K} (hx : x ≠ 0)
    (hy : y ≠ 0) (Px : IdxChangeP v (idxChangeDg i x)) (Pxy : IdxChangeP v (idxChangeDg i (x * y))) :
    IdxChangeP v (idxChangeDg i y) := by sorry
