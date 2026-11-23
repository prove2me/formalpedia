-- Prove2me | Theorems.Thm_Formalism_FG_KeyVAux_bd_mul_left
-- name    : Formalism.FG.KeyVAux.bd_mul_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:40:31.63413+00:00
-- url     : https://prove2.me/theorems/1fd5281c-b11d-4536-a78c-4d32d20c61f6
-- title:
--   Key VAux: bd mul left
-- statement:
--   The Key VAux construction uses the bd mul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/FunctionalEquationSubstVector.lean#L39-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/FunctionalEquationSubstVector.lean#L39-L48

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

theorem Formalism.FG.KeyVAux.bd_mul_left {τ : Type w} {C : ℝ} (hC : 0 ≤ C) {A B : MvPowerSeries τ K}
    (hA : IntegralMv A) (hB : Bd C B) : Bd C (A * B) := by sorry
