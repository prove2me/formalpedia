-- Prove2me | Theorems.Thm_CompanionTheory_Split_emb_loc
-- name    : CompanionTheory.Split.emb_loc
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:42:06.534067+00:00
-- url     : https://prove2.me/theorems/2a178e9f-e26e-4a1b-88ee-25265c74e683
-- title:
--   Split: emb loc
-- statement:
--   The Split construction uses the emb loc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/EqZeroOfCompAt.lean#L233-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/EqZeroOfCompAt.lean#L233-L234

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

theorem CompanionTheory.Split.emb_loc {x : GA L n} (hx : TrivOutside {s.v} x) : emb s n (s.loc n x) = x := by sorry
