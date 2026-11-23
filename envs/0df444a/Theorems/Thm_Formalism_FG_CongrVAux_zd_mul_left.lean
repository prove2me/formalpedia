-- Prove2me | Theorems.Thm_Formalism_FG_CongrVAux_zd_mul_left
-- name    : Formalism.FG.CongrVAux.zd_mul_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:37:19.378619+00:00
-- url     : https://prove2.me/theorems/e4cc6ba8-1345-442c-97cb-fdabab3b2fcb
-- title:
--   Congr VAux: zd mul left
-- statement:
--   The Congr VAux construction uses the zd mul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/CongrV.lean#L25-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/CongrV.lean#L25-L33

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
variable {R : Type u} [CommRing R] {τ : Type w}

theorem Formalism.FG.CongrVAux.zd_mul_left {d : τ →₀ ℕ} (x : MvPowerSeries τ R) {y : MvPowerSeries τ R} (hy : Zd d y) :
    Zd d (x * y) := by sorry
