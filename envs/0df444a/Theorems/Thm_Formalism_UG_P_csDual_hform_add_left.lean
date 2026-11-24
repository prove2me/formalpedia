-- Prove2me | Theorems.Thm_Formalism_UG_P_csDual_hform_add_left
-- name    : Formalism.UG.P.csDual_hform_add_left
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T03:58:12.28885+00:00
-- url     : https://prove2.me/theorems/f94676ec-3db2-4074-ba9b-2f3d48b02916
-- title:
--   P: cs Dual hform add left
-- statement:
--   The P construction uses the cs Dual hform add left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/CsDual.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/CsDual.lean#L15-L17

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsDual
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
open Formalism.UG

theorem Formalism.UG.P.csDual_hform_add_left {A : Type} [CommRing A] {n : Type} [Fintype n] (τ : A →+* A)
    (J : Matrix n n A) (u v y : n → A) : hform τ J (u + v) y = hform τ J u y + hform τ J v y := by sorry
