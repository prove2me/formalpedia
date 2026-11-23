-- Prove2me | Theorems.Thm_Formalism_DivisionValues_SemilocalBasisHermitianTwistDivisors_mem_hcompl
-- name    : Formalism.DivisionValues.SemilocalBasisHermitianTwistDivisors.mem_hcompl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:19:36.417804+00:00
-- url     : https://prove2.me/theorems/b8dfa738-0184-4678-b5a9-952058b41190
-- title:
--   Semilocal Basis Hermitian Twist Divisors: mem hcompl
-- statement:
--   The Semilocal Basis Hermitian Twist Divisors construction uses the mem hcompl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/LocBasis.lean#L20-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/LocBasis.lean#L20-L30

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

theorem Formalism.DivisionValues.SemilocalBasisHermitianTwistDivisors.mem_hcompl (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) (h1 : x ∉ w.asIdeal)
    (h2 : x ∉ (conjPl w).asIdeal) : x ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) w.asIdeal := by sorry
