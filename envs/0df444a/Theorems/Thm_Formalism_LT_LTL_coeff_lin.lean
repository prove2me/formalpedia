-- Prove2me | Theorems.Thm_Formalism_LT_LTL_coeff_lin
-- name    : Formalism.LT.LTL.coeff_lin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:39:07.415927+00:00
-- url     : https://prove2.me/theorems/7b69e2f9-d50e-490c-adc3-f709e06bad83
-- title:
--   LTL: coeff lin
-- statement:
--   The LTL construction uses the coeff lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/LTLemma.lean#L435-L437
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/LTLemma.lean#L435-L437

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

theorem Formalism.LT.LTL.coeff_lin (a : ι → K) (d : ι →₀ ℕ) :
    MvPowerSeries.coeff d (lin a) = ∑ i, a i * (if d = Finsupp.single i 1 then 1 else 0) := by sorry
