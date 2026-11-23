-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_toChoose
-- name    : Formalism.GM.gammaIntegralityLemmas.IVP.toChoose
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:49:38.180933+00:00
-- url     : https://prove2.me/theorems/8defc8e0-cc52-4045-b2de-f7e694052fce
-- title:
--   IVP: to Choose
-- statement:
--   The IVP construction uses the to Choose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L168-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L168-L197

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

theorem Formalism.GM.gammaIntegralityLemmas.IVP.toChoose {D S : ℕ} {g : ℕ → ℚ_[p]} (hg : IVP p D g) :
    ∃ c : ℕ → ℤ_[p], ∀ n, S ≤ n →
      g (n - S) = ∑ i ∈ range (D + 1), (c i : ℚ_[p]) * ((n.choose i : ℕ) : ℚ_[p]) := by sorry
