-- Prove2me | Theorems.Thm_CompanionTheory_Split_mem_UJ_one
-- name    : CompanionTheory.Split.mem_UJ_one
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:26:28.990336+00:00
-- url     : https://prove2.me/theorems/5dee3e79-07ac-476f-a826-f210342e03a3
-- title:
--   Split: mem UJ one
-- statement:
--   The Split construction uses the mem UJ one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/ExistsDenFin.lean#L41-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/ExistsDenFin.lean#L41-L45

import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_EqZeroOfCompAt
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_ExistsDenFin
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut TensorProduct Formalism.UG Formalism.L2
noncomputable section
open CompanionTheory CompanionTheory.Split
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
local notation3 "L⁺" => maximalRealSubfield L

theorem CompanionTheory.Split.mem_UJ_one {A : Type} [CommRing A] (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) (g : GL (Fin n) A) :
    g ∈ UJ σ (1 : Matrix (Fin n) (Fin n) A) ↔ g ∈ UGroup n σ hσ := by sorry
