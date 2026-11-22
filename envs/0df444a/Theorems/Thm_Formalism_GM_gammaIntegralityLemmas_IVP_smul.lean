-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_smul
-- name    : Formalism.GM.gammaIntegralityLemmas.IVP.smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:23:24.050582+00:00
-- url     : https://prove2.me/theorems/b2f0ce93-7f29-45a2-92fb-4ccf1c26f12e
-- title:
--   IVP: smul
-- statement:
--   The IVP construction uses the smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L52-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L52-L57

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

theorem Formalism.GM.gammaIntegralityLemmas.IVP.smul {D : ℕ} {g : ℕ → ℚ_[p]} (q : ℚ_[p]) (hq : ‖q‖ ≤ 1) (hg : IVP p D g) :
    IVP p D (fun m => q * g m) := by sorry
