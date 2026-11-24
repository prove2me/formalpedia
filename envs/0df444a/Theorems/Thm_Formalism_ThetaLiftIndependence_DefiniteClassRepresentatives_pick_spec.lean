-- Prove2me | Theorems.Thm_Formalism_ThetaLiftIndependence_DefiniteClassRepresentatives_pick_spec
-- name    : Formalism.ThetaLiftIndependence.DefiniteClassRepresentatives.pick_spec
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:29:22.422811+00:00
-- url     : https://prove2.me/theorems/fae3df3a-4d6b-45c7-9f37-19132344cdcd
-- title:
--   Definite Class Representatives: pick spec
-- statement:
--   The Definite Class Representatives construction uses the pick spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLiftIndependence/ThetaOrbitSums/ClassRepsDefinite.lean#L32-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLiftIndependence/ThetaOrbitSums/ClassRepsDefinite.lean#L32-L43

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

theorem Formalism.ThetaLiftIndependence.DefiniteClassRepresentatives.pick_spec (h : V →ₗ⋆[K] V →ₗ[K] K)
    (s₀ : Finset (Submodule (NumberField.RingOfIntegers K) V))
    {M : Submodule (NumberField.RingOfIntegers K) V} (hM : M ∈ s₀) :
    pick h s₀ (Quotient.mk (isoSetoid h) M) ∈ s₀ ∧
      Quotient.mk (isoSetoid h) (pick h s₀ (Quotient.mk (isoSetoid h) M)) =
        Quotient.mk (isoSetoid h) M := by sorry
