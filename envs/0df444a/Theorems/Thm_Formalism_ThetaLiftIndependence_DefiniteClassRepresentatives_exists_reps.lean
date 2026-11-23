-- Prove2me | Theorems.Thm_Formalism_ThetaLiftIndependence_DefiniteClassRepresentatives_exists_reps
-- name    : Formalism.ThetaLiftIndependence.DefiniteClassRepresentatives.exists_reps
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:13:38.25314+00:00
-- url     : https://prove2.me/theorems/cd7fdfa2-7c36-4180-83a5-a805e0114a22
-- title:
--   Definite Class Representatives: exists reps
-- statement:
--   The Definite Class Representatives construction uses the exists reps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLiftIndependence/ThetaOrbitSums/ClassRepsDefinite.lean#L45-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLiftIndependence/ThetaOrbitSums/ClassRepsDefinite.lean#L45-L77

import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_HermitianLattices_FinalNeighbourConstruct
import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_LatLiftIndep
import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_ClassRepsDefinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.ThetaLiftIndependence
open Formalism.ThetaLiftIndependence.DefiniteClassRepresentatives
open Formalism.HermitianLatticesTheory LatticeLiftIndependence
variable {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]

theorem Formalism.ThetaLiftIndependence.DefiniteClassRepresentatives.exists_reps (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (NumberField.RingOfIntegers K) V)
    (s₀ : Finset (Submodule (NumberField.RingOfIntegers K) V))
    (h₁ : ∀ M ∈ s₀, M ∈ genus h L) (h₂ : ∀ M ∈ genus h L, ∃ N ∈ s₀, ∃ g ∈ isom h, gmap g N = M) :
    ∃ s, IsClassReps h L s := by sorry
