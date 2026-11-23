-- Prove2me | Theorems.Thm_Formalism_UG_P_out_not_mem_of_ne_one
-- name    : Formalism.UG.P.out_not_mem_of_ne_one
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:26:58.435148+00:00
-- url     : https://prove2.me/theorems/ce035416-b9c5-4f61-ab3e-163dcdd20ee8
-- title:
--   P: out not mem of ne one
-- statement:
--   The P construction uses the out not mem of ne one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Heckebasic.lean#L73-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Heckebasic.lean#L73-L78

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Heckebasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {G : Type} [Group G]

theorem Formalism.UG.P.out_not_mem_of_ne_one (K : Subgroup G) (x : G ⧸ K) (hx : x ≠ ((1 : G) : G ⧸ K)) :
    x.out ∉ K := by sorry
