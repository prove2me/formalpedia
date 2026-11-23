-- Prove2me | Theorems.Thm_Formalism_FG_CongrVAux_divBy_mul_sub
-- name    : Formalism.FG.CongrVAux.divBy_mul_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:37:10.684817+00:00
-- url     : https://prove2.me/theorems/02adb1d8-b852-4a3c-82e4-51579cbaa3b7
-- title:
--   Congr VAux: div By mul sub
-- statement:
--   The Congr VAux construction uses the div By mul sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/CongrV.lean#L137-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/CongrV.lean#L137-L145

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CoeffV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CongrV
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
open Formalism Formalism.FG Formalism.FG.CongrVAux
open MvPowerSeries Formalism.G Formalism.LT Formalism.FG.SolveVAux
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {τ : Type w}

theorem Formalism.FG.CongrVAux.divBy_mul_sub {c : K} {a a' b b' : MvPowerSeries τ K} (ha' : IntegralMv a')
    (hb : IntegralMv b) (hab : DivByMv c (a - a')) (hbb : DivByMv c (b - b')) :
    DivByMv c (a * b - a' * b') := by sorry
