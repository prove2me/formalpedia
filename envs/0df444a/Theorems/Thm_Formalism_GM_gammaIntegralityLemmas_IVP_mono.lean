-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_mono
-- name    : Formalism.GM.gammaIntegralityLemmas.IVP.mono
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:49:40.920397+00:00
-- url     : https://prove2.me/theorems/ba18ef9a-8404-4125-aab1-c88f8db7b11f
-- title:
--   IVP: mono
-- statement:
--   The IVP construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L30-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L30-L32

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

theorem Formalism.GM.gammaIntegralityLemmas.IVP.mono {D D' : ℕ} {g : ℕ → ℚ_[p]} (h : IVP p D g) (hD : D ≤ D') : IVP p D' g := by sorry
