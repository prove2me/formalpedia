-- Prove2me | Theorems.Thm_Formalism_UG_P_mul_eq_out_mul
-- name    : Formalism.UG.P.mul_eq_out_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:33:27.883723+00:00
-- url     : https://prove2.me/theorems/90c1a44c-71d6-49e0-8a0b-3bf692e16da6
-- title:
--   P: mul eq out mul
-- statement:
--   The P construction uses the mul eq out mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FiniteCosetsInDoset.lean#L19-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FiniteCosetsInDoset.lean#L19-L33

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

theorem Formalism.UG.P.mul_eq_out_mul (K : Subgroup G) (s : G) (k : K) :
    ∃ k' : K, (k : G) * s =
      (((QuotientGroup.mk k : K ⧸ conjInter K s).out : K) : G) * s * k' := by sorry
