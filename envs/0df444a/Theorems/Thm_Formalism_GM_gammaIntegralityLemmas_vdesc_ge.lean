-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_vdesc_ge
-- name    : Formalism.GM.gammaIntegralityLemmas.vdesc_ge
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:51:02.12642+00:00
-- url     : https://prove2.me/theorems/317604ae-1712-434b-ad86-b18e18efa460
-- title:
--   gamma Integrality Lemmas: vdesc ge
-- statement:
--   The gamma Integrality Lemmas construction uses the vdesc ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L235-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L235-L239

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.gammaIntegralityLemmas
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem Formalism.GM.gammaIntegralityLemmas.vdesc_ge (x a : ℕ) (ha : a ≤ x) :
    padicValNat p a.factorial ≤ padicValNat p (x.descFactorial a) := by sorry
