-- Prove2me | Theorems.Thm_Formalism_DivisionValues_exponent_index_lattice_map_isLattice
-- name    : Formalism.DivisionValues.exponent_index_lattice.map_isLattice
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:19.868321+00:00
-- url     : https://prove2.me/theorems/549341ce-f6c3-4612-8890-5b2df3d49f85
-- title:
--   exponent index lattice: map is Lattice
-- statement:
--   The exponent index lattice construction uses the map is Lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/AuxStatement14.lean#L32-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/AuxStatement14.lean#L32-L36

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

theorem Formalism.DivisionValues.exponent_index_lattice.map_isLattice (P : V →ₗ[K] W) (hP : Function.Surjective P) (B : Submodule R V)
    (hB : Submodule.IsLattice K B) : Submodule.IsLattice K (B.map (P.restrictScalars R)) := by sorry
