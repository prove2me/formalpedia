-- Prove2me | Theorems.Thm_Formalism_UG_P_mem_stabAt_mul_iff
-- name    : Formalism.UG.P.mem_stabAt_mul_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:33:17.644622+00:00
-- url     : https://prove2.me/theorems/3ee1f7a9-2050-4453-a097-248446513491
-- title:
--   P: mem stab At mul iff
-- statement:
--   The P construction uses the mem stab At mul iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Ipindep.lean#L11-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Ipindep.lean#L11-L17

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Ipindep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {G : Type} [Group G]

theorem Formalism.UG.P.mem_stabAt_mul_iff (Γ K : Subgroup G) (g : G) (γ : Γ) (κ : K) (δ : Γ) :
    δ ∈ stabAt Γ K ((γ : G) * g * κ) ↔ γ⁻¹ * δ * γ ∈ stabAt Γ K g := by sorry
