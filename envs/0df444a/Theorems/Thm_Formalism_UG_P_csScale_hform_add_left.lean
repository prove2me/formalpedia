-- Prove2me | Theorems.Thm_Formalism_UG_P_csScale_hform_add_left
-- name    : Formalism.UG.P.csScale_hform_add_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:22:14.634414+00:00
-- url     : https://prove2.me/theorems/99ea04cc-56ef-4389-b703-ca213d2e3eea
-- title:
--   P: cs Scale hform add left
-- statement:
--   The P construction uses the cs Scale hform add left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/CsScale.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/CsScale.lean#L17-L19

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

theorem Formalism.UG.P.csScale_hform_add_left (σ : A →+* A) (J : Matrix n n A) (x x' y : n → A) :
    hform σ J (x + x') y = hform σ J x y + hform σ J x' y := by sorry
