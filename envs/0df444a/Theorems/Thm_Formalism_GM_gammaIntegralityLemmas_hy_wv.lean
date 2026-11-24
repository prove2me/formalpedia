-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_hy_wv
-- name    : Formalism.GM.gammaIntegralityLemmas.hy_wv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:23:31.657751+00:00
-- url     : https://prove2.me/theorems/61722bb6-e1f1-4f17-87ba-16c9e3d68905
-- title:
--   gamma Integrality Lemmas: hy wv
-- statement:
--   The gamma Integrality Lemmas construction uses the hy wv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L1466-L1470
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L1466-L1470

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

theorem Formalism.GM.gammaIntegralityLemmas.hy_wv (ρ : Fin r) : ∀ c ∈ univ.erase ρ, wv (N := N) c ≠ ev ρ ∧ ev (N := N) c ≠ ev ρ := by sorry
