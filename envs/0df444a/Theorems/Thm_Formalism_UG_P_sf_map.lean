-- Prove2me | Theorems.Thm_Formalism_UG_P_sf_map
-- name    : Formalism.UG.P.sf_map
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:34:09.737829+00:00
-- url     : https://prove2.me/theorems/eea4dbed-09fc-4dc3-a208-922259f2e8cb
-- title:
--   P: sf map
-- statement:
--   The P construction uses the sf map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Stabfin.lean#L67-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Stabfin.lean#L67-L75

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

theorem Formalism.UG.P.sf_map {E : Type} [CommRing E] (σ : E →+* E) (τ : E →+* ℂ)
    (hτ : τ.comp σ = (starRingEnd ℂ).comp τ) (J : Matrix n n E) (x y : n → E) :
    τ (hform σ J x y) = hform (starRingEnd ℂ) (J.map τ) (fun k => τ (x k)) (fun k => τ (y k)) := by sorry
