-- Prove2me | Theorems.Thm_Formalism_FG_CongrVAux_coeff_ofFun
-- name    : Formalism.FG.CongrVAux.coeff_ofFun
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:37:01.471979+00:00
-- url     : https://prove2.me/theorems/c418374f-fca1-48c2-82d3-87855bf3f58c
-- title:
--   Congr VAux: coeff of Fun
-- statement:
--   The Congr VAux construction uses the coeff of Fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/CongrV.lean#L214-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/CongrV.lean#L214-L214

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

theorem Formalism.FG.CongrVAux.coeff_ofFun (g : (τ →₀ ℕ) → K) (e : τ →₀ ℕ) : coeff e (ofFun g) = g e := by sorry
