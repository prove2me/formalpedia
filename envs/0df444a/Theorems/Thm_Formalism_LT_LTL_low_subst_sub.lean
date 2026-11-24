-- Prove2me | Theorems.Thm_Formalism_LT_LTL_low_subst_sub
-- name    : Formalism.LT.LTL.low_subst_sub
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T09:51:08.276626+00:00
-- url     : https://prove2.me/theorems/a61338fe-463d-4a15-9519-2ee5e5a5f200
-- title:
--   LTL: low subst sub
-- statement:
--   The LTL construction uses the low subst sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/LTLemma.lean#L56-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/LTLemma.lean#L56-L77

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
variable {K : Type u} [NormedField K] {ι : Type*}

theorem Formalism.LT.LTL.low_subst_sub [Finite ι] {τ : Type*} {a b : ι → MvPowerSeries τ K}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0)
    (hab : ∀ i, Near 1 (a i) (b i)) {N : ℕ} {δ : MvPowerSeries ι K} (hδ : Low N δ) :
    Low (N + 1) (MvPowerSeries.subst a δ - MvPowerSeries.subst b δ) := by sorry
