-- Prove2me | Theorems.Thm_CompanionTheory_HeckeA_op_comm_same
-- name    : CompanionTheory.HeckeA.op_comm_same
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:32:00.737854+00:00
-- url     : https://prove2.me/theorems/e2e8c44a-4324-409d-b3b6-1a71ef5c7e1b
-- title:
--   Hecke A: op comm same
-- statement:
--   The Hecke A construction uses the op comm same property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/HeckeA.lean#L59-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/HeckeA.lean#L59-L70

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeActMem
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Heckebasic
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EvalFg
import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_HeckeA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG Formalism.UG.P
noncomputable section
open CompanionTheory CompanionTheory.HeckeA
variable {G H W : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W] (ι : H →* G) (K : Subgroup H)
variable {K}

theorem CompanionTheory.HeckeA.op_comm_same (hK : IsCommensurated K) {φ ψ : H → ℂ} (hφ : φ ∈ Hecke ℂ K) (hψ : ψ ∈ Hecke ℂ K)
    (hc : conv K φ ψ = conv K ψ φ) {f : G → W} (hf : Inv ι K f) : op ι K φ (op ι K ψ f) = op ι K ψ (op ι K φ f) := by sorry
