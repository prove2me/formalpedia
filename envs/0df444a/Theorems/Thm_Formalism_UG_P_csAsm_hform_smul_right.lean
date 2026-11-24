-- Prove2me | Theorems.Thm_Formalism_UG_P_csAsm_hform_smul_right
-- name    : Formalism.UG.P.csAsm_hform_smul_right
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:33:10.731621+00:00
-- url     : https://prove2.me/theorems/523f6349-7c0f-4bca-a534-da39eec9df1b
-- title:
--   P: cs Asm hform smul right
-- statement:
--   The P construction uses the cs Asm hform smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/CsAsmHformSmulRight.lean#L13-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/CsAsmHformSmulRight.lean#L13-L17

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_LevelSubgroupFiniteAdelicStandard
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsAsmHformSmulRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG Formalism.UG.CS

theorem Formalism.UG.P.csAsm_hform_smul_right {E : Type} [Field E] (σ : E →+* E) {n : Type} [Fintype n]
    (J : Matrix n n E) (c : E) (y x : n → E) :
    hform σ J y (c • x) = c * hform σ J y x := by sorry
