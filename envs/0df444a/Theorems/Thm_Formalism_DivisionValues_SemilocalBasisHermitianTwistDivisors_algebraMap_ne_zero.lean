-- Prove2me | Theorems.Thm_Formalism_DivisionValues_SemilocalBasisHermitianTwistDivisors_algebraMap_ne_zero
-- name    : Formalism.DivisionValues.SemilocalBasisHermitianTwistDivisors.algebraMap_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:19:07.453979+00:00
-- url     : https://prove2.me/theorems/cc583678-8791-418f-80a9-9e5b7e5eefa5
-- title:
--   Semilocal Basis Hermitian Twist Divisors: algebra Map ne zero
-- statement:
--   The Semilocal Basis Hermitian Twist Divisors construction uses the algebra Map ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/LocBasis.lean#L48-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/LocBasis.lean#L48-L50

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.SemilocalBasisHermitianTwistDivisors
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem Formalism.DivisionValues.SemilocalBasisHermitianTwistDivisors.algebraMap_ne_zero (w : HeightOneSpectrum (𝓞 K)) {s : 𝓞 K}
    (hs : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) w.asIdeal) : algebraMap (𝓞 K) K s ≠ 0 := by sorry
