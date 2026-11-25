-- Prove2me | Theorems.Thm_CompanionTheory_Split_reps_Umax
-- name    : CompanionTheory.Split.reps_Umax
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:35:59.64563+00:00
-- url     : https://prove2.me/theorems/30c9ebaf-2009-49e5-97b4-3f184a8c7091
-- title:
--   Split: reps Umax
-- statement:
--   The Split construction uses the reps Umax property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/ExistsDenFin.lean#L47-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/ExistsDenFin.lean#L47-L78

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

theorem CompanionTheory.Split.reps_Umax : ∃ T : Set (GA L n), T.Finite ∧ ∀ g, ∃ γ ∈ GQ L n, ∃ t ∈ T, ∃ κ ∈ Umax L n, g = γ * t * κ := by sorry
