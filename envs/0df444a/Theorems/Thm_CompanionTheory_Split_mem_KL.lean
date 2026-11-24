-- Prove2me | Theorems.Thm_CompanionTheory_Split_mem_KL
-- name    : CompanionTheory.Split.mem_KL
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:42:11.141494+00:00
-- url     : https://prove2.me/theorems/f2980f79-4adf-4ee6-b4c2-5ce33c0f146e
-- title:
--   Split: mem KL
-- statement:
--   The Split construction uses the mem KL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/EqZeroOfCompAt.lean#L187-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/EqZeroOfCompAt.lean#L187-L198

import Definitions.Def_ReciprocityTheory_Automorphisms_SplitCoeAlgebraMap
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsIntegerUnitSplitPlaceConjugatePrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CmFieldAdeleSplitPlaceSupportIntegral
import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_EqZeroOfCompAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut TensorProduct
noncomputable section
open CompanionTheory CompanionTheory.Split
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
local notation3 "L⁺" => maximalRealSubfield L
variable (s : SplitPlace L)

theorem CompanionTheory.Split.mem_KL {g : GL (Fin n) (s.v.adicCompletion L⁺)} : g ∈ KL s n ↔
    (∀ i j, Valued.v ((g : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) i j) ≤ 1) ∧
      ∀ i j, Valued.v (((g⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) i j) ≤ 1 := by sorry
