-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_fock_add_left
-- name    : Formalism.GM.gammaIntegralityLemmas.fock_add_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:23:43.006273+00:00
-- url     : https://prove2.me/theorems/4043b890-b57e-4a92-8e03-736dd4ac27c4
-- title:
--   gamma Integrality Lemmas: fock add left
-- statement:
--   The gamma Integrality Lemmas construction uses the fock add left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L316-L321
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L316-L321

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

theorem Formalism.GM.gammaIntegralityLemmas.fock_add_left (F F' G : MvPolynomial σ ℚ_[p]) :
    Formalism.GM.M.fock p (F + F') G = Formalism.GM.M.fock p F G + Formalism.GM.M.fock p F' G := by sorry
