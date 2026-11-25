-- Prove2me | Theorems.Thm_CompanionTheory_Split_exists_den_fin
-- name    : CompanionTheory.Split.exists_den_fin
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:25:57.252964+00:00
-- url     : https://prove2.me/theorems/a558aa51-19cd-4341-8cbf-21314add8b5e
-- title:
--   Split: exists den fin
-- statement:
--   The Split construction uses the exists den fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/ExistsDenFin.lean#L32-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/ExistsDenFin.lean#L32-L39

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

theorem CompanionTheory.Split.exists_den_fin {T : Set (GA L n)} (hT : T.Finite) :
    ∃ c : ℕ, c ≠ 0 ∧ ∀ t ∈ T, ∀ i j, (c : AL L) * ent t i j ∈ ALint L := by sorry
