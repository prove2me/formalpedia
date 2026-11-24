-- Prove2me | Theorems.Thm_Formalism_LT_LTL_divBy_subst_sub
-- name    : Formalism.LT.LTL.divBy_subst_sub
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T09:51:05.045664+00:00
-- url     : https://prove2.me/theorems/993fafdb-2234-495a-9edf-fdcec20d18eb
-- title:
--   LTL: div By subst sub
-- statement:
--   The LTL construction uses the div By subst sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/LTLemma.lean#L248-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/LTLemma.lean#L248-L262

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

theorem Formalism.LT.LTL.divBy_subst_sub [Finite ι] {τ : Type*} {c : K} {a b : ι → MvPowerSeries τ K}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0)
    (hab : ∀ i, Cong c (a i) (b i)) {δ : MvPowerSeries ι K} (hδ : IntegralMv δ) :
    DivByMv c (MvPowerSeries.subst a δ - MvPowerSeries.subst b δ) := by sorry
