-- Prove2me | Theorems.Thm_Formalism_UG_P_sf_single
-- name    : Formalism.UG.P.sf_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:11:15.041265+00:00
-- url     : https://prove2.me/theorems/409d0d79-39b7-4a1a-87bf-b42212f5a487
-- title:
--   P: sf single
-- statement:
--   The P construction uses the sf single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Stabfin.lean#L83-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Stabfin.lean#L83-L91

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabfin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField ComplexConjugate
open Formalism Formalism.UG Formalism.UG.P
variable {n : Type} [Fintype n] [DecidableEq n]

theorem Formalism.UG.P.sf_single {A : Type} [CommRing A] (σ : A →+* A) (J : Matrix n n A) (i : n) (y : n → A) :
    hform σ J (Pi.single i 1) y = (J *ᵥ y) i := by sorry
