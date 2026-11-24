-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_fock_E_pow
-- name    : Formalism.GM.gammaIntegralityLemmas.fock_E_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:23:03.659021+00:00
-- url     : https://prove2.me/theorems/dc2a7080-970b-4c2a-94a2-9b9f2ce70ba0
-- title:
--   gamma Integrality Lemmas: fock E pow
-- statement:
--   The gamma Integrality Lemmas construction uses the fock E pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L378-L383
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L378-L383

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
variable {σ : Type} [Fintype σ] [DecidableEq σ] {r : ℕ} (w e : Fin r → σ)

theorem Formalism.GM.gammaIntegralityLemmas.fock_E_pow (j : ℕ) (g h : MvPolynomial σ ℚ_[p]) :
    Formalism.GM.M.fock p ((Formalism.GM.tieE w e ^ j) g) h = Formalism.GM.M.fock p g ((Formalism.GM.tieF w e ^ j) h) := by sorry
