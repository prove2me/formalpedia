-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z2_plane_ring_half
-- name    : Formalism.L2.SG.Pf.LatDictZ.Z2.plane_ring_half
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T16:58:17.12883+00:00
-- url     : https://prove2.me/theorems/643db0f9-401e-4243-8a43-56cfad81a1d7
-- title:
--   Z2: plane ring half
-- statement:
--   The Z2 construction uses the plane ring half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LatDictZPlane.lean#L40-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LatDictZPlane.lean#L40-L86

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZPlane
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z2
open ReciprocityTheory.ChartRestriction.L3.WA
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]

theorem Formalism.L2.SG.Pf.LatDictZ.Z2.plane_ring_half {S : Subring K} {P Q : K → Prop} (hP : IdealLike S P) (hQ : IdealLike S Q)
    (hunit : ∀ a ∈ S, ¬ P a → ¬ Q a → IsUnitIn S a)
    {ε η γ α β c μ : K} (hε : ε ∈ S) (hη : η ∈ S) (hα : α ∈ S) (hβ : β ∈ S) (hc : c ∈ S)
    (hμ : IsUnitIn S μ) (hγ : α * ε + β * η + γ = 1) (hPε : P ε) (hPη : P η) :
    IsUnitIn S (γ + ε + c * η) ∨ IsUnitIn S (γ + ε + (c + μ) * η) ∨
      IsUnitIn S (γ + c * ε + η) ∨ IsUnitIn S (γ + (c + μ) * ε + η) := by sorry
