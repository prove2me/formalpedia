-- Prove2me | Theorems.Thm_Formalism_UG_P_out_smul
-- name    : Formalism.UG.P.out_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:17:29.599139+00:00
-- url     : https://prove2.me/theorems/426534c2-3ed1-46cd-a236-5aa0fc67d815
-- title:
--   P: out smul
-- statement:
--   The P construction uses the out smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/HeckeActMem.lean#L11-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/HeckeActMem.lean#L11-L19

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeActMem
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

theorem Formalism.UG.P.out_smul (K : Subgroup G) (c : G) (x : G ⧸ K) :
    ∃ κ : K, (c • x).out = c * x.out * (κ : G) := by sorry
