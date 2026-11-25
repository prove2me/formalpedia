-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_FT_commute
-- name    : Formalism.GM.gammaIntegralityLemmas.FT_commute
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:49:19.078696+00:00
-- url     : https://prove2.me/theorems/094826b7-1edc-4732-86c7-ff7a11f38dba
-- title:
--   gamma Integrality Lemmas: FT commute
-- statement:
--   The gamma Integrality Lemmas construction uses the FT commute property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L513-L514
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L513-L514

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
open MvPolynomial Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {σ : Type} [DecidableEq σ] {r : ℕ} (w e : Fin r → σ)

theorem Formalism.GM.gammaIntegralityLemmas.FT_commute (u v : σ) (T : Finset (Fin r)) : Commute (Dop (p := p) u v) (FT w e T) := by sorry
