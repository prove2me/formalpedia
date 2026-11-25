-- Prove2me | Theorems.Thm_Formalism_FG_KeyVAux_bd_add
-- name    : Formalism.FG.KeyVAux.bd_add
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:25:01.668817+00:00
-- url     : https://prove2.me/theorems/4348ab59-10f4-4149-9f7a-1bf61b8a8b1b
-- title:
--   Key VAux: bd add
-- statement:
--   The Key VAux construction uses the bd add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/FunctionalEquationSubstVector.lean#L36-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/FunctionalEquationSubstVector.lean#L36-L37

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_NormSigmaLeOne
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CoeffV
import Definitions.Def_Lemmata_MultivariateIntegrals_IntegralMv
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FunctionalEquationSubstVector
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
open Formalism Formalism.FG Formalism.FG.KeyVAux
open Formalism.G Formalism.LT
variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem Formalism.FG.KeyVAux.bd_add {τ : Type w} {C : ℝ} {A B : MvPowerSeries τ K} (hA : Bd C A) (hB : Bd C B) :
    Bd C (A + B) := by sorry
