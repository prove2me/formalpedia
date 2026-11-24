-- Prove2me | Theorems.Thm_CompanionTheory_Split_commute_of_ne
-- name    : CompanionTheory.Split.commute_of_ne
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:48:22.959594+00:00
-- url     : https://prove2.me/theorems/2e543404-35e8-4c42-989e-27e69ffa375c
-- title:
--   Split: commute of ne
-- statement:
--   The Split construction uses the commute of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/EqZeroOfCompAt.lean#L240-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/EqZeroOfCompAt.lean#L240-L249

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

theorem CompanionTheory.Split.commute_of_ne {v v' : HeightOneSpectrum (𝓞 L⁺)} (h : v ≠ v') {x y : GA L n} (hx : TrivOutside {v} x)
    (hy : TrivOutside {v'} y) : x * y = y * x := by sorry
