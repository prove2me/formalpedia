-- Prove2me | Theorems.Thm_Formalism_DivisionValues_exponent_index_lattice_nondeg_of_adj
-- name    : Formalism.DivisionValues.exponent_index_lattice.nondeg_of_adj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:23:05.231733+00:00
-- url     : https://prove2.me/theorems/ef89054d-adb6-40d3-9320-35e619b92d7f
-- title:
--   exponent index lattice: nondeg of adj
-- statement:
--   The exponent index lattice construction uses the nondeg of adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/AuxStatement14.lean#L285-L293
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/AuxStatement14.lean#L285-L293

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ClassSumDualLe
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_RatHerm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionLemmaFirst
import Definitions.Def_Lemmata_HermitianVanishing_KeyZero
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_AuxStatement14
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
open exponent_index_lattice RationalHermitianForm
open Formalism.DivisionValues.exponent_index_lattice
variable {K V W : Type} [Field K] [StarRing K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

theorem Formalism.DivisionValues.exponent_index_lattice.nondeg_of_adj (hV : V →ₗ⋆[K] V →ₗ[K] K) (hVn : hV.Nondegenerate)
    (hW : W →ₗ⋆[K] W →ₗ[K] K) (hWs : hW.IsSymm) (E : W →ₗ[K] V) (P : V →ₗ[K] W)
    (adj : ∀ x z, hW (P x) z = hV x (E z)) (hE : Function.Injective E) : hW.Nondegenerate := by sorry
