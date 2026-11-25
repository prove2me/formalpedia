-- Prove2me | Theorems.Thm_CompanionTheory_Split_pow_mul_mem
-- name    : CompanionTheory.Split.pow_mul_mem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:32:31.392607+00:00
-- url     : https://prove2.me/theorems/1b639ca4-e9ba-407f-831c-70de70492da3
-- title:
--   Split: pow mul mem
-- statement:
--   The Split construction uses the pow mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/ExistsDenFin.lean#L171-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/ExistsDenFin.lean#L171-L192

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

theorem CompanionTheory.Split.pow_mul_mem {p : ℕ} (hp : s.Above p) {z : AL L} (hz : ∀ w, w ≠ s.v → compAt L w z = 0) :
    ∃ a : ℕ, ((p ^ a : ℕ) : AL L) * z ∈ ALint L := by sorry
