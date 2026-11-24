-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z3_mem_orth
-- name    : Formalism.L2.SG.Pf.LatDictZ.Z3.mem_orth
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T14:43:16.207671+00:00
-- url     : https://prove2.me/theorems/f9fabce7-6e88-4272-941b-c5d8d7ae07a4
-- title:
--   Z3: mem orth
-- statement:
--   The Z3 construction uses the mem orth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LatDictZZLoc.lean#L31-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LatDictZZLoc.lean#L31-L32

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

theorem Formalism.L2.SG.Pf.LatDictZ.Z3.mem_orth {h : V →ₗ⋆[K] V →ₗ[K] K} {P : Submodule K V} {x : V} :
    x ∈ orth h P ↔ ∀ q ∈ P, h q x = 0 := by sorry
