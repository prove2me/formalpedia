-- Prove2me | Theorems.Thm_Formalism_DivisionValues_exponent_index_lattice_dual_map
-- name    : Formalism.DivisionValues.exponent_index_lattice.dual_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:33:30.429257+00:00
-- url     : https://prove2.me/theorems/2c07a6ff-9219-4acd-b077-e62e5d673ae0
-- title:
--   exponent index lattice: dual map
-- statement:
--   The exponent index lattice construction uses the dual map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/AuxStatement14.lean#L24-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/AuxStatement14.lean#L24-L30

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

theorem Formalism.DivisionValues.exponent_index_lattice.dual_map (hV : V →ₗ⋆[K] V →ₗ[K] K) (hW : W →ₗ⋆[K] W →ₗ[K] K) (E : W →ₗ[K] V)
    (P : V →ₗ[K] W) (adj : ∀ x z, hW (P x) z = hV x (E z)) (A : Submodule R V) :
    Formalism.HermitianLatticesTheory.dual hW (A.map (P.restrictScalars R)) =
      (Formalism.HermitianLatticesTheory.dual hV A).comap (E.restrictScalars R) := by sorry
