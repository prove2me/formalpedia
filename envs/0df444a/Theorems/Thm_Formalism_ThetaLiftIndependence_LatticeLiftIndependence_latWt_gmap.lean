-- Prove2me | Theorems.Thm_Formalism_ThetaLiftIndependence_LatticeLiftIndependence_latWt_gmap
-- name    : Formalism.ThetaLiftIndependence.LatticeLiftIndependence.latWt_gmap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:13:15.513034+00:00
-- url     : https://prove2.me/theorems/38b49cc3-2192-496e-a0a3-37e5328aa954
-- title:
--   Lattice Lift Independence: lat Wt gmap
-- statement:
--   The Lattice Lift Independence construction uses the lat Wt gmap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLiftIndependence/ThetaOrbitSums/LatLiftIndep.lean#L57-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLiftIndependence/ThetaOrbitSums/LatLiftIndep.lean#L57-L60

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

theorem Formalism.ThetaLiftIndependence.LatticeLiftIndependence.latWt_gmap (h : V →ₗ⋆[K] V →ₗ[K] K) {g : V ≃ₗ[K] V} (hg : g ∈ isom h)
    (M : Submodule (NumberField.RingOfIntegers K) V) : latWt h (gmap g M) = latWt h M := by sorry
