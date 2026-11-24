-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z3_isSelfDualMod_res
-- name    : Formalism.L2.SG.Pf.LatDictZ.Z3.isSelfDualMod_res
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T15:37:28.889517+00:00
-- url     : https://prove2.me/theorems/4c78e0d8-9287-4cb6-bc50-6539521e160a
-- title:
--   Z3: is Self Dual Mod res
-- statement:
--   The Z3 construction uses the is Self Dual Mod res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LatDictZZLoc.lean#L78-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LatDictZZLoc.lean#L78-L102

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

theorem Formalism.L2.SG.Pf.LatDictZ.Z3.isSelfDualMod_res (hM : IsSelfDualMod S h M) (hsp : Splits h P M) :
    IsSelfDualMod S (h.domRestrict₁₂ (orth h P) (orth h P))
      (M.comap (orth h P).subtype.toAddMonoidHom) := by sorry
