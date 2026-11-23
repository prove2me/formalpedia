-- Prove2me | Theorems.Thm_Formalism_UG_P_csScale_hform_smul_left
-- name    : Formalism.UG.P.csScale_hform_smul_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:24:09.955431+00:00
-- url     : https://prove2.me/theorems/7c53e0f2-c3f9-4f77-893b-32346e078d30
-- title:
--   P: cs Scale hform smul left
-- statement:
--   The P construction uses the cs Scale hform smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/CsScale.lean#L33-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/CsScale.lean#L33-L37

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsScale
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
variable {A : Type} [CommRing A] {n : Type} [Fintype n]

theorem Formalism.UG.P.csScale_hform_smul_left (σ : A →+* A) (J : Matrix n n A) (c : A) (x y : n → A) :
    hform σ J (c • x) y = σ c * hform σ J x y := by sorry
