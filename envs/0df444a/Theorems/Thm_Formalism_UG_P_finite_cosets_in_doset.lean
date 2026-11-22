-- Prove2me | Theorems.Thm_Formalism_UG_P_finite_cosets_in_doset
-- name    : Formalism.UG.P.finite_cosets_in_doset
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T17:20:17.930008+00:00
-- url     : https://prove2.me/theorems/106106cb-6397-494f-a0c2-2aabfadf8970
-- title:
--   P: finite cosets in doset
-- statement:
--   The P construction uses the finite cosets in doset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FiniteCosetsInDoset.lean#L35-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FiniteCosetsInDoset.lean#L35-L50

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FiniteCosetsInDoset
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

theorem Formalism.UG.P.finite_cosets_in_doset {K : Subgroup G} (hK : IsCommensurated K) (s : G) :
    {x : G ⧸ K | ∃ a b : K, x.out = (a : G) * s * b}.Finite := by sorry
