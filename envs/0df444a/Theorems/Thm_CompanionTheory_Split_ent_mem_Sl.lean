-- Prove2me | Theorems.Thm_CompanionTheory_Split_ent_mem_Sl
-- name    : CompanionTheory.Split.ent_mem_Sl
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:26:39.095534+00:00
-- url     : https://prove2.me/theorems/0674d8b6-b4ef-4a5c-b662-e3ce084fd2ed
-- title:
--   Split: ent mem Sl
-- statement:
--   The Split construction uses the ent mem Sl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/ExistsDenFin.lean#L214-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/ExistsDenFin.lean#L214-L221

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
variable (s : SplitPlace L)

theorem CompanionTheory.Split.ent_mem_Sl {l : ℕ} (hl : l.Prime) (hs : ¬ s.Above l) {x : GA L n} (hx : TrivOutside {s.v} x) (i j : Fin n) :
    ent x i j ∈ Sl L hl := by sorry
