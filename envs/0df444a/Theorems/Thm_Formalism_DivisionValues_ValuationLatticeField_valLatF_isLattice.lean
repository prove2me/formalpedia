-- Prove2me | Theorems.Thm_Formalism_DivisionValues_ValuationLatticeField_valLatF_isLattice
-- name    : Formalism.DivisionValues.ValuationLatticeField.valLatF_isLattice
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:34:57.919475+00:00
-- url     : https://prove2.me/theorems/43957ad7-45f1-45ad-bc86-c1c678b6ef1e
-- title:
--   Valuation Lattice Field: val Lat F is Lattice
-- statement:
--   The Valuation Lattice Field construction uses the val Lat F is Lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ClassSumDualGeOfFamily.lean#L103-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ClassSumDualGeOfFamily.lean#L103-L134

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
open exponent_index_lattice ValuationLatticeField
open Formalism.DivisionValues.ValuationLatticeField

theorem Formalism.DivisionValues.ValuationLatticeField.valLatF_isLattice {K : Type} [Field K] [NumberField K] [StarRing K]
    {n : ℕ} {Cl V : Type} [Fintype Cl] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (I : (Fin n → K) →ₗ[K] (Cl → V))
    (hI : Function.Injective I) (N : Cl → Submodule (𝓞 K) V) (hN : ∀ c, Submodule.IsLattice K (N c)) :
    Submodule.IsLattice K (valLatF I N) := by sorry
