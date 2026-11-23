-- Prove2me | Theorems.Thm_Formalism_DivisionValues_SemilocalBasisHermitianTwistDivisors_mem_A
-- name    : Formalism.DivisionValues.SemilocalBasisHermitianTwistDivisors.mem_A
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:19:08.390156+00:00
-- url     : https://prove2.me/theorems/95ead3fe-58a1-4d6b-b8e4-82f32e55f869
-- title:
--   Semilocal Basis Hermitian Twist Divisors: mem A
-- statement:
--   The Semilocal Basis Hermitian Twist Divisors construction uses the mem A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/LocBasis.lean#L43-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/LocBasis.lean#L43-L46

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

theorem Formalism.DivisionValues.SemilocalBasisHermitianTwistDivisors.mem_A (w : HeightOneSpectrum (𝓞 K)) (x : K) :
    x ∈ A w ↔ ∃ (a s : 𝓞 K) (_ : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) w.asIdeal),
      x = algebraMap (𝓞 K) K a * (algebraMap (𝓞 K) K s)⁻¹ := by sorry
