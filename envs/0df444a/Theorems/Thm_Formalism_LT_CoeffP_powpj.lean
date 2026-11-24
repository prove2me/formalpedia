-- Prove2me | Theorems.Thm_Formalism_LT_CoeffP_powpj
-- name    : Formalism.LT.CoeffP.powpj
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T09:50:44.797719+00:00
-- url     : https://prove2.me/theorems/fa5c39a8-264c-48ac-a938-b15914fc66fb
-- title:
--   Coeff P: powpj
-- statement:
--   The Coeff P construction uses the powpj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/SigmaNormLeOne.lean#L192-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/SigmaNormLeOne.lean#L192-L199

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u v
open Formalism Formalism.LT Formalism.LT.CoeffP
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type v}

theorem Formalism.LT.CoeffP.powpj {p : ℕ} (hp : p.Prime) {r : ℕ} (hr : 1 ≤ r) {A B : MvPowerSeries ι K}
    (hA : Bd 1 A) (hB : Bd 1 B) (hD : Bd (‖(p : K)‖ ^ r) (A - B)) :
    ∀ j : ℕ, Bd (‖(p : K)‖ ^ (r + j)) (A ^ (p ^ j) - B ^ (p ^ j))
  := by sorry
