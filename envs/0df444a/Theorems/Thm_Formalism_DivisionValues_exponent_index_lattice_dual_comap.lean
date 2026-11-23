-- Prove2me | Theorems.Thm_Formalism_DivisionValues_exponent_index_lattice_dual_comap
-- name    : Formalism.DivisionValues.exponent_index_lattice.dual_comap
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:33:38.237715+00:00
-- url     : https://prove2.me/theorems/ac2cb1af-b14f-44dd-8679-98132dc97c7e
-- title:
--   exponent index lattice: dual comap
-- statement:
--   The exponent index lattice construction uses the dual comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/AuxStatement14.lean#L38-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/AuxStatement14.lean#L38-L63

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
open Formalism.DivisionValues.exponent_index_lattice
variable {R K V W : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  [AddCommGroup W] [Module K W] [Module R W] [IsScalarTower R K W]

theorem Formalism.DivisionValues.exponent_index_lattice.dual_comap [IsDedekindDomain R] [IsFractionRing R K] [FiniteDimensional K V]
    [FiniteDimensional K W] (hV : V →ₗ⋆[K] V →ₗ[K] K) (hVs : hV.IsSymm) (hVn : hV.Nondegenerate)
    (hW : W →ₗ⋆[K] W →ₗ[K] K) (hWs : hW.IsSymm)
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K))
    (E : W →ₗ[K] V) (P : V →ₗ[K] W) (adj : ∀ x z, hW (P x) z = hV x (E z))
    (hE : Function.Injective E) (hP : Function.Surjective P)
    (A : Submodule R V) (hA : Submodule.IsLattice K A) :
    Formalism.HermitianLatticesTheory.dual hW (A.comap (E.restrictScalars R)) =
      (Formalism.HermitianLatticesTheory.dual hV A).map (P.restrictScalars R) := by sorry
