-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z2_plane_prim
-- name    : Formalism.L2.SG.Pf.LatDictZ.Z2.plane_prim
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T16:58:03.256102+00:00
-- url     : https://prove2.me/theorems/bf69db40-9621-427d-8cd6-51e58e1524dd
-- title:
--   Z2: plane prim
-- statement:
--   The Z2 construction uses the plane prim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LatDictZPlane.lean#L178-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LatDictZPlane.lean#L178-L212

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

theorem Formalism.L2.SG.Pf.LatDictZ.Z2.plane_prim {S : Subring K} (hS : IsHermSemilocal S) (B : V →ₗ⋆[K] V →ₗ[K] K)
    {N : AddSubgroup V} (hsm : ∀ a ∈ S, ∀ m ∈ N, a • m ∈ N) (hint : ∀ x ∈ N, ∀ y ∈ N, B x y ∈ S)
    {z w : V} (hz : z ∈ N) (hzw : B z w = 1) (hspan : ∃ t : K, t ≠ 0 ∧ t • w ∈ N) :
    ∃ α : K, α ≠ 0 ∧ α • w ∈ N ∧ ∀ c : K, c • (α • w) ∈ N → c ∈ S := by sorry
