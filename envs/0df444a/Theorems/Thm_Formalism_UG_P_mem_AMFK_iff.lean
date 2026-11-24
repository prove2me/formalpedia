-- Prove2me | Theorems.Thm_Formalism_UG_P_mem_AMFK_iff
-- name    : Formalism.UG.P.mem_AMFK_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:33:25.282509+00:00
-- url     : https://prove2.me/theorems/bd92d900-63db-4262-909e-eb1b58fa1993
-- title:
--   P: mem AMFK iff
-- statement:
--   The P construction uses the mem AMFK iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/AutomorphicFormsDecompositionHolds.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/AutomorphicFormsDecompositionHolds.lean#L13-L15

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AutomorphicFormsDecompositionHolds
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
variable {G : Type} [Group G] (Γ K : Subgroup G)

theorem Formalism.UG.P.mem_AMFK_iff {k : Type} [CommRing k] {W : Type} [AddCommGroup W] [Module k W]
    (ρK : Representation k K W) (f : G → W) :
    f ∈ AMFK k Γ K ρK ↔ ∀ γ : Γ, ∀ g : G, ∀ κ : K, f ((γ : G) * g * κ) = ρK κ⁻¹ (f g) := by sorry
