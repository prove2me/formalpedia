-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_fock_sum_right
-- name    : Formalism.GM.gammaIntegralityLemmas.fock_sum_right
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T20:33:05.833652+00:00
-- url     : https://prove2.me/theorems/f34443e1-8e36-4015-94fd-4e285d00a597
-- title:
--   gamma Integrality Lemmas: fock sum right
-- statement:
--   The gamma Integrality Lemmas construction uses the fock sum right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L338-L340
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L338-L340

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

theorem Formalism.GM.gammaIntegralityLemmas.fock_sum_right {ι : Type} (t : Finset ι) (F : MvPolynomial σ ℚ_[p]) (G : ι → MvPolynomial σ ℚ_[p]) :
    Formalism.GM.M.fock p F (∑ i ∈ t, G i) = ∑ i ∈ t, Formalism.GM.M.fock p F (G i) := by sorry
