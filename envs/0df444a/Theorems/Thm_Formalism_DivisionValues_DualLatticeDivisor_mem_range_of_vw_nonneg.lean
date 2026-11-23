-- Prove2me | Theorems.Thm_Formalism_DivisionValues_DualLatticeDivisor_mem_range_of_vw_nonneg
-- name    : Formalism.DivisionValues.DualLatticeDivisor.mem_range_of_vw_nonneg
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:13:16.485793+00:00
-- url     : https://prove2.me/theorems/6cc7cd9a-78d0-40e9-8707-03ff92311c19
-- title:
--   Dual Lattice Divisor: mem range of vw nonneg
-- statement:
--   The Dual Lattice Divisor construction uses the mem range of vw nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/DivIntoDual.lean#L17-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/DivIntoDual.lean#L17-L45

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_DivIntoDual
import Definitions.Def_Formalism_QuotientMetricDivisors_ReductionLemmaZero
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DivIntoDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.DualLatticeDivisor
variable {K : Type} [Field K] [NumberField K]

theorem Formalism.DivisionValues.DualLatticeDivisor.mem_range_of_vw_nonneg (a : K) (ha : a ≠ 0)
    (h : ∀ w : HeightOneSpectrum (𝓞 K), 0 ≤ vw w a) :
    a ∈ Set.range (algebraMap (𝓞 K) K) := by sorry
