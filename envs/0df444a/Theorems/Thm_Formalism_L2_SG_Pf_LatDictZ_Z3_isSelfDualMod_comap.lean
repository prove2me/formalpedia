-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z3_isSelfDualMod_comap
-- name    : Formalism.L2.SG.Pf.LatDictZ.Z3.isSelfDualMod_comap
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T16:57:56.311912+00:00
-- url     : https://prove2.me/theorems/eded20e5-2a0b-41e8-a96b-571d2853292d
-- title:
--   Z3: is Self Dual Mod comap
-- statement:
--   The Z3 construction uses the is Self Dual Mod comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LatDictZZLoc.lean#L179-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LatDictZZLoc.lean#L179-L203

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

theorem Formalism.L2.SG.Pf.LatDictZ.Z3.isSelfDualMod_comap (F : V ≃ₗ[K] V) (hF : ∀ x y, h (F x) (F y) = h x y)
    (hM : IsSelfDualMod S h M) : IsSelfDualMod S h (M.comap F.symm.toLinearMap.toAddMonoidHom) := by sorry
