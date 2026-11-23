-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_FT_insert
-- name    : Formalism.GM.gammaIntegralityLemmas.FT_insert
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:49:19.946834+00:00
-- url     : https://prove2.me/theorems/e927067c-10f0-420d-b8af-65860ec46d5d
-- title:
--   gamma Integrality Lemmas: FT insert
-- statement:
--   The gamma Integrality Lemmas construction uses the FT insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L501-L503
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L501-L503

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

theorem Formalism.GM.gammaIntegralityLemmas.FT_insert (c : Fin r) (T : Finset (Fin r)) (hc : c ∉ T) :
    FT (p := p) w e (insert c T) = Dop (w c) (e c) + FT w e T := by sorry
