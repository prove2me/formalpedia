-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z3_hyz_one
-- name    : Formalism.L2.SG.Pf.LatDictZ.Z3.hyz_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T14:58:55.457829+00:00
-- url     : https://prove2.me/theorems/b8bf0544-63ac-4699-bc5a-62757c8d93b8
-- title:
--   Z3: hyz one
-- statement:
--   The Z3 construction uses the hyz one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LatDictZZLoc.lean#L212-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LatDictZZLoc.lean#L212-L215

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

theorem Formalism.L2.SG.Pf.LatDictZ.Z3.hyz_one (hs : h.IsSymm) {z y : V} (hzy : h z y = 1) : h y z = 1 := by sorry
