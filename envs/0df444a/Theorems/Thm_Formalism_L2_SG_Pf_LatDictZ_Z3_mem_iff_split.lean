-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z3_mem_iff_split
-- name    : Formalism.L2.SG.Pf.LatDictZ.Z3.mem_iff_split
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T16:59:11.179745+00:00
-- url     : https://prove2.me/theorems/8e6098f2-5fee-4ba0-b8e0-20a550860b51
-- title:
--   Z3: mem iff split
-- statement:
--   The Z3 construction uses the mem iff split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LatDictZZLoc.lean#L120-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LatDictZZLoc.lean#L120-L136

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

theorem Formalism.L2.SG.Pf.LatDictZ.Z3.mem_iff_split {Q : Submodule K V} (hc : IsCompl P Q)
    (hsp : ∀ w ∈ M, ∃ w₁ ∈ M, w₁ ∈ P ∧ w - w₁ ∈ Q) (x : V) :
    x ∈ M ↔ (((Submodule.prodEquivOfIsCompl P Q hc).symm x).1 : V) ∈ M ∧
      (((Submodule.prodEquivOfIsCompl P Q hc).symm x).2 : V) ∈ M := by sorry
