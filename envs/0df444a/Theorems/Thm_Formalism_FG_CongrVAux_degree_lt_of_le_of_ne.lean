-- Prove2me | Theorems.Thm_Formalism_FG_CongrVAux_degree_lt_of_le_of_ne
-- name    : Formalism.FG.CongrVAux.degree_lt_of_le_of_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:36:56.154514+00:00
-- url     : https://prove2.me/theorems/f5aca6b7-30ac-460c-a602-9b560da4fe34
-- title:
--   Congr VAux: degree lt of le of ne
-- statement:
--   The Congr VAux construction uses the degree lt of le of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/CongrV.lean#L201-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/CongrV.lean#L201-L210

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

theorem Formalism.FG.CongrVAux.degree_lt_of_le_of_ne {e d : τ →₀ ℕ} (hle : e ≤ d) (hne : e ≠ d) :
    e.degree < d.degree := by sorry
