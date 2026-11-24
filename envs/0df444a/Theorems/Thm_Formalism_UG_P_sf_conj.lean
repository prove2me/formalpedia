-- Prove2me | Theorems.Thm_Formalism_UG_P_sf_conj
-- name    : Formalism.UG.P.sf_conj
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:34:01.720803+00:00
-- url     : https://prove2.me/theorems/6e806c5e-b9b3-414a-9826-b32b8fb09049
-- title:
--   P: sf conj
-- statement:
--   The P construction uses the sf conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Stabfin.lean#L47-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Stabfin.lean#L47-L54

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

theorem Formalism.UG.P.sf_conj (A : Matrix n n ℂ) (hA : ∀ i j, conj (A j i) = A i j) (u v : n → ℂ) :
    conj (hform (starRingEnd ℂ) A u v) = hform (starRingEnd ℂ) A v u := by sorry
