-- Prove2me | Theorems.Thm_Formalism_UG_P_finite_support_cosets
-- name    : Formalism.UG.P.finite_support_cosets
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:18:06.064187+00:00
-- url     : https://prove2.me/theorems/eeec435d-392b-4c21-b563-b04ce3f823fb
-- title:
--   P: finite support cosets
-- statement:
--   The P construction uses the finite support cosets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FiniteCosetsInDoset.lean#L52-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FiniteCosetsInDoset.lean#L52-L59

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

theorem Formalism.UG.P.finite_support_cosets {k : Type} [Zero k] {K : Subgroup G} (hK : IsCommensurated K)
    {f : G → k} (hf : FinDosetSupp K f) :
    {x : G ⧸ K | f x.out ≠ 0}.Finite := by sorry
