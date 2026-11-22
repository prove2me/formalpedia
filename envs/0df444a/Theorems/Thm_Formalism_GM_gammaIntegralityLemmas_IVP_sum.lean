-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_sum
-- name    : Formalism.GM.gammaIntegralityLemmas.IVP.sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:30:40.643683+00:00
-- url     : https://prove2.me/theorems/427bf794-ffea-4816-bc43-e046a852e693
-- title:
--   IVP: sum
-- statement:
--   The IVP construction uses the sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L59-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L59-L66

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
open Finset Polynomial
variable {p : ℕ} [Fact p.Prime]

theorem Formalism.GM.gammaIntegralityLemmas.IVP.sum {ι : Type} {D : ℕ} (s : Finset ι) (g : ι → ℕ → ℚ_[p]) (h : ∀ i ∈ s, IVP p D (g i)) :
    IVP p D (fun m => ∑ i ∈ s, g i m) := by sorry
