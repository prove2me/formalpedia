-- Prove2me | Theorems.Thm_Formalism_DivisionValues_SemilocalBasisHermitianTwistDivisors_mem_loc_iff_span
-- name    : Formalism.DivisionValues.SemilocalBasisHermitianTwistDivisors.mem_loc_iff_span
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:19:17.579927+00:00
-- url     : https://prove2.me/theorems/aaecd97c-b643-40c6-bfa0-e3422fd374f4
-- title:
--   Semilocal Basis Hermitian Twist Divisors: mem loc iff span
-- statement:
--   The Semilocal Basis Hermitian Twist Divisors construction uses the mem loc iff span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/LocBasis.lean#L75-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/LocBasis.lean#L75-L104

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

theorem Formalism.DivisionValues.SemilocalBasisHermitianTwistDivisors.mem_loc_iff_span (w : HeightOneSpectrum (𝓞 K)) {d : ℕ} (M : Submodule (𝓞 K) (Fin d → K))
    (x : Fin d → K) :
    x ∈ Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal M ↔ x ∈ Submodule.span (A w) (M : Set (Fin d → K)) := by sorry
