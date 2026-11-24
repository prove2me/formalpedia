-- Prove2me | Theorems.Thm_Formalism_summable_abs_a
-- name    : Formalism.summable_abs_a
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:45:15.601635+00:00
-- url     : https://prove2.me/theorems/9d4f70d2-f381-487d-807b-1db8591a6793
-- title:
--   Formalism: summable abs a
-- statement:
--   The Formalism construction uses the summable abs a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/MellinSgen.lean#L78-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/MellinSgen.lean#L78-L97

import Definitions.Def_Formalism_DefsOC
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSAux
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSgen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology ArithmeticFunction
noncomputable section
open Formalism
variable (a : ℕ → ℝ)

theorem Formalism.summable_abs_a (K : ℝ) (hK : ∀ n : ℕ, |a n| ≤ K * vonMangoldt n) {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => |a n| * (n : ℝ) ^ (-σ)) := by sorry
