-- Prove2me | Theorems.Thm_CompanionTheory_HeckeA_op_conj
-- name    : CompanionTheory.HeckeA.op_conj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:31:53.839798+00:00
-- url     : https://prove2.me/theorems/d18b794b-a828-4e7a-b353-07e34e38815d
-- title:
--   Hecke A: op conj
-- statement:
--   The Hecke A construction uses the op conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/HeckeA.lean#L72-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/HeckeA.lean#L72-L82

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

theorem CompanionTheory.HeckeA.op_conj {φ : H → ℂ} (hφ : IsBiInv K φ) {f : G → W} (hf : Inv ι K f) {κ : G} {u : H} (hu : u ∈ K) {c : ℂ}
    (hκ : ∀ h, κ * ι h * κ⁻¹ = ι (u * h * u⁻¹)) (hc : ∀ g, f (g * κ) = c • f g) (hfin : IsCommensurated K)
    (hφ' : φ ∈ Hecke ℂ K) (g : G) : op ι K φ f (g * κ) = c • op ι K φ f g := by sorry
