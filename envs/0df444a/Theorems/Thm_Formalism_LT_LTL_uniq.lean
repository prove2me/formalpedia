-- Prove2me | Theorems.Thm_Formalism_LT_LTL_uniq
-- name    : Formalism.LT.LTL.uniq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T09:51:56.761673+00:00
-- url     : https://prove2.me/theorems/d853961f-f521-480a-89d1-e83a13e280fc
-- title:
--   LTL: uniq
-- statement:
--   The LTL construction uses the uniq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/LTLemma.lean#L551-L611
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/LTLemma.lean#L551-L611

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

theorem Formalism.LT.LTL.uniq (hS : LTSetting K p q π) (he : IsLTSeries q π e) (he' : IsLTSeries q π e')
    {ψ φ : MvPowerSeries ι K} (hψ0 : MvPowerSeries.constantCoeff ψ = 0)
    (hφ0 : MvPowerSeries.constantCoeff φ = 0)
    (h1 : ∀ i, MvPowerSeries.coeff (Finsupp.single i 1) ψ =
      MvPowerSeries.coeff (Finsupp.single i 1) φ)
    (hLψ : Ldef e e' ψ = 0) (hLφ : Ldef e e' φ = 0) : ψ = φ := by sorry
