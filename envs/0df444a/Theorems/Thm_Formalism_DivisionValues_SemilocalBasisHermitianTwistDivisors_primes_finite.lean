-- Prove2me | Theorems.Thm_Formalism_DivisionValues_SemilocalBasisHermitianTwistDivisors_primes_finite
-- name    : Formalism.DivisionValues.SemilocalBasisHermitianTwistDivisors.primes_finite
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:19:15.414012+00:00
-- url     : https://prove2.me/theorems/d78649c3-7cb4-4217-85f7-d0792fd539ed
-- title:
--   Semilocal Basis Hermitian Twist Divisors: primes finite
-- statement:
--   The Semilocal Basis Hermitian Twist Divisors construction uses the primes finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/LocBasis.lean#L52-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/LocBasis.lean#L52-L73

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

theorem Formalism.DivisionValues.SemilocalBasisHermitianTwistDivisors.primes_finite (w : HeightOneSpectrum (𝓞 K)) :
    {P : Ideal (A w) | P.IsPrime}.Finite := by sorry
