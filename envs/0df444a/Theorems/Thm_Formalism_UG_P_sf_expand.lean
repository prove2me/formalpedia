-- Prove2me | Theorems.Thm_Formalism_UG_P_sf_expand
-- name    : Formalism.UG.P.sf_expand
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:34:04.269806+00:00
-- url     : https://prove2.me/theorems/60e2bcb5-c712-4be9-990e-5da7ee4cf01d
-- title:
--   P: sf expand
-- statement:
--   The P construction uses the sf expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Stabfin.lean#L37-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Stabfin.lean#L37-L45

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

theorem Formalism.UG.P.sf_expand (A : Matrix n n ℂ) (a b : ℂ) (u v : n → ℂ) :
    hform (starRingEnd ℂ) A (a • v + b • u) (a • v + b • u) =
      conj a * a * hform (starRingEnd ℂ) A v v + conj a * b * hform (starRingEnd ℂ) A v u +
      conj b * a * hform (starRingEnd ℂ) A u v + conj b * b * hform (starRingEnd ℂ) A u u := by sorry
