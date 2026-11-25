-- Prove2me | Theorems.Thm_CompanionTheory_Split_reps_Cong
-- name    : CompanionTheory.Split.reps_Cong
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:35:06.41751+00:00
-- url     : https://prove2.me/theorems/d5454907-3bd4-452f-8f85-79ecdc447676
-- title:
--   Split: reps Cong
-- statement:
--   The Split construction uses the reps Cong property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/ExistsDenFin.lean#L80-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/ExistsDenFin.lean#L80-L101

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

theorem CompanionTheory.Split.reps_Cong {N : ℕ} (hN : N ≠ 0) :
    ∃ T : Set (GA L n), T.Finite ∧ ∀ u ∈ Umax L n, ∃ t ∈ T, NG.Cong L n N (t⁻¹ * u) := by sorry
