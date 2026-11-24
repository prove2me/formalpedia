-- Prove2me | Theorems.Thm_Formalism_ThetaLiftIndependence_LatticeLiftIndependence_reps_inv
-- name    : Formalism.ThetaLiftIndependence.LatticeLiftIndependence.reps_inv
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:29:00.538043+00:00
-- url     : https://prove2.me/theorems/b42be10a-7cc1-418c-bead-eff25a679ab6
-- title:
--   Lattice Lift Independence: reps inv
-- statement:
--   The Lattice Lift Independence construction uses the reps inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLiftIndependence/ThetaOrbitSums/LatLiftIndep.lean#L62-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLiftIndependence/ThetaOrbitSums/LatLiftIndep.lean#L62-L70

import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_LatLiftIndep
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
open Formalism.ThetaLiftIndependence.LatticeLiftIndependence
open Formalism.HermitianLatticesTheory
variable {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]

theorem Formalism.ThetaLiftIndependence.LatticeLiftIndependence.reps_inv (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (NumberField.RingOfIntegers K) V)
    {s : Finset (Submodule (NumberField.RingOfIntegers K) V)} (hs : IsClassReps h L s)
    {N N' N'' : Submodule (NumberField.RingOfIntegers K) V} (hN : N ∈ s) (hN'' : N'' ∈ s)
    {g g' : V ≃ₗ[K] V} (hg : g ∈ isom h) (hg' : g' ∈ isom h)
    (e : gmap g N' = N) (e' : gmap g' N'' = N') : N'' = N := by sorry
