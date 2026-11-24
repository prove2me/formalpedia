-- Prove2me | Theorems.Thm_Formalism_UG_P_mk_of_eq
-- name    : Formalism.UG.P.mk_of_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:33:23.822836+00:00
-- url     : https://prove2.me/theorems/9b921475-19d2-4da4-9d67-edd22860226f
-- title:
--   P: mk of eq
-- statement:
--   The P construction uses the mk of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/AutomorphicFormsDecompositionHolds.lean#L23-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/AutomorphicFormsDecompositionHolds.lean#L23-L30

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

theorem Formalism.UG.P.mk_of_eq (s : ClassSet Γ K → G) (hs : ∀ c, DoubleCoset.mk Γ K (s c) = c)
    (c : ClassSet Γ K) (g : G) (γ : Γ) (κ : K) (e : g = (γ : G) * s c * κ) :
    DoubleCoset.mk Γ K g = c := by sorry
