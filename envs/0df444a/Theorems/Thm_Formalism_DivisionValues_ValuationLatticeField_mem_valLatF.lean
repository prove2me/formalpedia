-- Prove2me | Theorems.Thm_Formalism_DivisionValues_ValuationLatticeField_mem_valLatF
-- name    : Formalism.DivisionValues.ValuationLatticeField.mem_valLatF
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:34:51.440528+00:00
-- url     : https://prove2.me/theorems/62ad9f25-d7a1-450a-97fe-2e782df3998c
-- title:
--   Valuation Lattice Field: mem val Lat F
-- statement:
--   The Valuation Lattice Field construction uses the mem val Lat F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ClassSumDualGeOfFamily.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ClassSumDualGeOfFamily.lean#L16-L19

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ClassSumDualGeF
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_AuxStatement14
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.ValuationLatticeField
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem Formalism.DivisionValues.ValuationLatticeField.mem_valLatF {n : ℕ} {Cl V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (I : (Fin n → K) →ₗ[K] (Cl → V)) (N : Cl → Submodule (𝓞 K) V)
    (x : Fin n → K) : x ∈ valLatF I N ↔ ∀ c, I x c ∈ N c := by sorry
