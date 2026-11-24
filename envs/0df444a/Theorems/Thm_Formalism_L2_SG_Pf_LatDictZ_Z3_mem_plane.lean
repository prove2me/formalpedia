-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z3_mem_plane
-- name    : Formalism.L2.SG.Pf.LatDictZ.Z3.mem_plane
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T16:57:26.828279+00:00
-- url     : https://prove2.me/theorems/e582da5e-8a05-4c22-ad0c-ada87ba2d9fc
-- title:
--   Z3: mem plane
-- statement:
--   The Z3 construction uses the mem plane property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LatDictZZLoc.lean#L247-L274
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LatDictZZLoc.lean#L247-L274

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZZLoc
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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z3
open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA Formalism.L2.SG.Pf.LatDictZ.Z0
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {P : Submodule K V} {S : Subring K} {M M₁ M₂ : AddSubgroup V}

theorem Formalism.L2.SG.Pf.LatDictZ.Z3.mem_plane (hs : h.IsSymm) (hM : IsSelfDualMod S h M) {z y : V} (hz : z ∈ M) (hy : y ∈ M)
    (hzy : h z y = 1) (hD : IsUnitIn S (1 - h z z * h y y)) (α β : K) :
    α • z + β • y ∈ M ↔ α ∈ S ∧ β ∈ S := by sorry
