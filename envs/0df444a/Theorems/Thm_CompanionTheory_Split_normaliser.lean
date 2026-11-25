-- Prove2me | Theorems.Thm_CompanionTheory_Split_normaliser
-- name    : CompanionTheory.Split.normaliser
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:33:35.08187+00:00
-- url     : https://prove2.me/theorems/bad660c7-cd77-46a6-bca2-f4e347abdd72
-- title:
--   Split: normaliser
-- statement:
--   The Split construction uses the normaliser property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/ExistsDenFin.lean#L114-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/ExistsDenFin.lean#L114-L160

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

theorem CompanionTheory.Split.normaliser {ϖ : s.v.adicCompletion L⁺} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ))
    (t : GL (Fin n) (s.v.adicCompletion L⁺)) (ht : ∀ k ∈ KL s n, t * k * t⁻¹ ∈ KL s n) :
    ∃ u ∈ KL s n, ∀ h, t * h * t⁻¹ = u * h * u⁻¹ := by sorry
