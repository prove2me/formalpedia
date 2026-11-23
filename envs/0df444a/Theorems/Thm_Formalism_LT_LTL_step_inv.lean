-- Prove2me | Theorems.Thm_Formalism_LT_LTL_step_inv
-- name    : Formalism.LT.LTL.step_inv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:39:14.504073+00:00
-- url     : https://prove2.me/theorems/f3d9eed9-a8f6-444b-895b-ad5b177aea47
-- title:
--   LTL: step inv
-- statement:
--   The LTL construction uses the step inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/LTLemma.lean#L470-L508
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/LTLemma.lean#L470-L508

import Definitions.Def_Formalism_TorsionNormIteration_LTLemma
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_LTLemma
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
open Formalism Formalism.LT Formalism.LT.LTL
open Formalism.G Formalism.G.LogCR Formalism.LT.InvIntP
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type*}
variable [Fintype ι] [DecidableEq ι]
variable {p q : ℕ} {π : K} {e e' : PowerSeries K} {a : ι → K}

theorem Formalism.LT.LTL.step_inv (hS : LTSetting K p q π) (he : IsLTSeries q π e) (he' : IsLTSeries q π e')
    {N : ℕ} (hN : 1 ≤ N) {P : MvPowerSeries ι K} (h : Inv e e' a N P) :
    Inv e e' a (N + 1) (P + corr e e' π N P) ∧ Low (N + 1) (corr e e' π N P) := by sorry
