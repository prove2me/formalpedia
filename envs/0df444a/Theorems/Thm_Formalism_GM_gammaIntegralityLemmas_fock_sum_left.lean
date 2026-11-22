-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_fock_sum_left
-- name    : Formalism.GM.gammaIntegralityLemmas.fock_sum_left
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T20:32:48.411811+00:00
-- url     : https://prove2.me/theorems/d7af3f9e-d66a-4d99-b02b-27ef4bf4abcf
-- title:
--   gamma Integrality Lemmas: fock sum left
-- statement:
--   The gamma Integrality Lemmas construction uses the fock sum left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L331-L336
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L331-L336

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
variable {σ : Type} [Fintype σ] [DecidableEq σ]

theorem Formalism.GM.gammaIntegralityLemmas.fock_sum_left {ι : Type} (t : Finset ι) (F : ι → MvPolynomial σ ℚ_[p]) (G : MvPolynomial σ ℚ_[p]) :
    Formalism.GM.M.fock p (∑ i ∈ t, F i) G = ∑ i ∈ t, Formalism.GM.M.fock p (F i) G := by sorry
