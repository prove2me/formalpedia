-- Prove2me | Theorems.Thm_CompanionTheory_HeckeA_coset_sum_eq
-- name    : CompanionTheory.HeckeA.coset_sum_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:31:58.480797+00:00
-- url     : https://prove2.me/theorems/214baa71-12d8-4bac-844d-4cb98dfb93b1
-- title:
--   Hecke A: coset sum eq
-- statement:
--   The Hecke A construction uses the coset sum eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/HeckeA.lean#L18-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/HeckeA.lean#L18-L49

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
open Classical

theorem CompanionTheory.HeckeA.coset_sum_eq (J : Subgroup G) (hJ : ∀ h, ι h ∈ J ↔ h ∈ K) (d : H) {f : G → W} (hf : Inv ι K f) (g : G)
    {D : Set G} (hD : ∀ x, x ∈ D ↔ ∃ h ∈ DoubleCoset.doubleCoset d (K : Set H) K, ι h = x) :
    (∑ᶠ c : G ⧸ J, if hc : ∃ x ∈ D, (x : G ⧸ J) = c then f (g * hc.choose) else 0) = op ι K (dosetInd ℂ K d) f g := by sorry
