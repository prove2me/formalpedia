-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_tieF_split
-- name    : Formalism.GM.gammaIntegralityLemmas.tieF_split
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:23:32.009519+00:00
-- url     : https://prove2.me/theorems/dfe0de7a-b0bb-4d7a-8bfa-d3697236d32b
-- title:
--   gamma Integrality Lemmas: tie F split
-- statement:
--   The gamma Integrality Lemmas construction uses the tie F split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L505-L507
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L505-L507

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

theorem Formalism.GM.gammaIntegralityLemmas.tieF_split (ρ : Fin r) :
    Formalism.GM.tieF w e = Dop (p := p) (w ρ) (e ρ) + FT w e (univ.erase ρ) := by sorry
