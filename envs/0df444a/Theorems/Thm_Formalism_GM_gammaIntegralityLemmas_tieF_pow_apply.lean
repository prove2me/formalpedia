-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_tieF_pow_apply
-- name    : Formalism.GM.gammaIntegralityLemmas.tieF_pow_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:23:17.213166+00:00
-- url     : https://prove2.me/theorems/be38cf89-c7d3-4ac9-b68f-c1aa94f085a6
-- title:
--   gamma Integrality Lemmas: tie F pow apply
-- statement:
--   The gamma Integrality Lemmas construction uses the tie F pow apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L1418-L1425
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L1418-L1425

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
variable {σ : Type} [Fintype σ] [DecidableEq σ] {r : ℕ} (w e : Fin r → σ) (ρ : Fin r)

theorem Formalism.GM.gammaIntegralityLemmas.tieF_pow_apply (j : ℕ) (Z : MvPolynomial σ ℚ_[p]) :
    (Formalism.GM.tieF w e ^ j) Z = ∑ a ∈ range (j + 1),
      ((j.choose a : ℕ) : ℚ_[p]) • (Dop (w ρ) (e ρ) ^ a) ((FT w e (univ.erase ρ) ^ (j - a)) Z) := by sorry
