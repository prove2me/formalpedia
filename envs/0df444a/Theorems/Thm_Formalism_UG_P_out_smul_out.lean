-- Prove2me | Theorems.Thm_Formalism_UG_P_out_smul_out
-- name    : Formalism.UG.P.out_smul_out
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:33:20.496939+00:00
-- url     : https://prove2.me/theorems/0b46f825-7833-4b1c-a3e0-fbaa701e5fa7
-- title:
--   P: out smul out
-- statement:
--   The P construction uses the out smul out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/HeckeAssoc.lean#L12-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/HeckeAssoc.lean#L12-L18

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AssocFin
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeAssoc
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
variable {G : Type} [Group G] (K : Subgroup G)

theorem Formalism.UG.P.out_smul_out (h : G) (z : G ⧸ K) : ∃ c : K, (h • z : G ⧸ K).out = h * z.out * c := by sorry
