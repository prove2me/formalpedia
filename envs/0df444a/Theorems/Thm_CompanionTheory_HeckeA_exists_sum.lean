-- Prove2me | Theorems.Thm_CompanionTheory_HeckeA_exists_sum
-- name    : CompanionTheory.HeckeA.exists_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:29:39.744803+00:00
-- url     : https://prove2.me/theorems/c385366d-796a-415f-b45a-36364e74fa66
-- title:
--   Hecke A: exists sum
-- statement:
--   The Hecke A construction uses the exists sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/HeckeA.lean#L53-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/HeckeA.lean#L53-L57

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

theorem CompanionTheory.HeckeA.exists_sum (hK : IsCommensurated K) {φ : H → ℂ} (hφ : φ ∈ Hecke ℂ K) :
    ∃ S : Finset (H ⧸ K), ∀ (f : G → W) (g : G), op ι K φ f g = ∑ c ∈ S, φ c.out • f (g * ι c.out) := by sorry
