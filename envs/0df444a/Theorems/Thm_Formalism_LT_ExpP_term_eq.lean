-- Prove2me | Theorems.Thm_Formalism_LT_ExpP_term_eq
-- name    : Formalism.LT.ExpP.term_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T09:51:22.834686+00:00
-- url     : https://prove2.me/theorems/5e72ca73-c27a-47a8-a0f8-b54c34076649
-- title:
--   Exp P: term eq
-- statement:
--   The Exp P construction uses the term eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/NormNatCastOfNotDvd.lean#L133-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/NormNatCastOfNotDvd.lean#L133-L139

import Definitions.Def_Formalism_TorsionNormIteration_Statement
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_NormNatCastOfNotDvd
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
universe u
open Formalism Formalism.LT Formalism.LT.ExpP
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem Formalism.LT.ExpP.term_eq (p c : K) (d m : ℕ) :
    c • ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ^ m * (p • MvPowerSeries.X 1) ^ (d - m) *
      (d.choose m : MvPowerSeries (Fin 2) K)) =
    (c * (p ^ (d - m) * (d.choose m : K))) •
      ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ^ m * MvPowerSeries.X 1 ^ (d - m)) := by sorry
