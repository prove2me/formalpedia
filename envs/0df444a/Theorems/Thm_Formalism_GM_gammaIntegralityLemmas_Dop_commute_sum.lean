-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_Dop_commute_sum
-- name    : Formalism.GM.gammaIntegralityLemmas.Dop_commute_sum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T22:23:13.775004+00:00
-- url     : https://prove2.me/theorems/53699f37-2893-4ade-8445-bb4db5536140
-- title:
--   gamma Integrality Lemmas: Dop commute sum
-- statement:
--   The gamma Integrality Lemmas construction uses the Dop commute sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L412-L414
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L412-L414

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
variable {σ : Type} [DecidableEq σ]

theorem Formalism.GM.gammaIntegralityLemmas.Dop_commute_sum {ι : Type} (s : Finset ι) (u v : σ) (f g : ι → σ) :
    Commute (Dop (p := p) u v) (∑ i ∈ s, Dop (f i) (g i)) := by sorry
