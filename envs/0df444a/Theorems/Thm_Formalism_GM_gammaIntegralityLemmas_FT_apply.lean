-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_FT_apply
-- name    : Formalism.GM.gammaIntegralityLemmas.FT_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:49:22.988036+00:00
-- url     : https://prove2.me/theorems/f13337fe-d138-49cf-9aca-bf4329c83985
-- title:
--   gamma Integrality Lemmas: FT apply
-- statement:
--   The gamma Integrality Lemmas construction uses the FT apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L509-L511
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L509-L511

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

theorem Formalism.GM.gammaIntegralityLemmas.FT_apply (T : Finset (Fin r)) (H : MvPolynomial σ ℚ_[p]) :
    FT (p := p) w e T H = ∑ c ∈ T, Dop (w c) (e c) H := by sorry
