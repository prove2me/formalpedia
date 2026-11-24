-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_kap_ge
-- name    : Formalism.GM.gammaIntegralityLemmas.kap_ge
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:23:13.704679+00:00
-- url     : https://prove2.me/theorems/d2419bf3-bd62-474b-a1b4-457d58be0e1a
-- title:
--   gamma Integrality Lemmas: kap ge
-- statement:
--   The gamma Integrality Lemmas construction uses the kap ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L1135-L1144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L1135-L1144

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
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [hp : Fact p.Prime]
variable {N r : ℕ}

theorem Formalism.GM.gammaIntegralityLemmas.kap_ge (N r B : ℕ) (hr : 1 ≤ r) : (N + 4) * (r * B) + 6 * B ≤ kap N r B := by sorry
