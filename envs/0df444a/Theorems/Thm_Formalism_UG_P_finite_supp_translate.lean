-- Prove2me | Theorems.Thm_Formalism_UG_P_finite_supp_translate
-- name    : Formalism.UG.P.finite_supp_translate
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:31:30.640799+00:00
-- url     : https://prove2.me/theorems/b52b8bdb-db80-453c-9711-d03964597dd7
-- title:
--   P: finite supp translate
-- statement:
--   The P construction uses the finite supp translate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/AssocFin.lean#L37-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/AssocFin.lean#L37-L51

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AssocFin
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

theorem Formalism.UG.P.finite_supp_translate (hK : IsCommensurated K) {k : Type} [Zero k] (f : G → k)
    (hf : FinDosetSupp K f) (h : G) :
    {x : G ⧸ K | f (h * x.out) ≠ 0}.Finite := by sorry
