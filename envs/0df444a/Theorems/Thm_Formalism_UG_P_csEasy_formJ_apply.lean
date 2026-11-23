-- Prove2me | Theorems.Thm_Formalism_UG_P_csEasy_formJ_apply
-- name    : Formalism.UG.P.csEasy_formJ_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:22:25.436668+00:00
-- url     : https://prove2.me/theorems/f8e0affd-29a7-481a-a6b6-86f629176bb2
-- title:
--   P: cs Easy form J apply
-- statement:
--   The P construction uses the cs Easy form J apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/CsEasy.lean#L49-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/CsEasy.lean#L49-L58

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsEasy
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix NumberField
open Formalism Formalism.UG Formalism.UG.P

theorem Formalism.UG.P.csEasy_formJ_apply {E : Type} [Field E] (σ : E →+* E) (hσ : ∀ e, σ (σ e) = e)
    {n : Type} [Fintype n] [DecidableEq n] (J : Matrix n n E) (c : E) (x y : n → E) :
    Formalism.UG.CS.formJ σ hσ J c x y = c * Formalism.UG.hform σ J x y := by sorry
