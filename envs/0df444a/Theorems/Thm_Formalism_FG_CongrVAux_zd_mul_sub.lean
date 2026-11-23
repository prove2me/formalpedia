-- Prove2me | Theorems.Thm_Formalism_FG_CongrVAux_zd_mul_sub
-- name    : Formalism.FG.CongrVAux.zd_mul_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:37:04.528154+00:00
-- url     : https://prove2.me/theorems/b3c7dcb9-dafc-4eb4-b8e3-b3ecff5b1222
-- title:
--   Congr VAux: zd mul sub
-- statement:
--   The Congr VAux construction uses the zd mul sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/CongrV.lean#L35-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/CongrV.lean#L35-L39

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

theorem Formalism.FG.CongrVAux.zd_mul_sub {d : τ →₀ ℕ} {a a' b b' : MvPowerSeries τ R} (ha : Zd d (a - a'))
    (hb : Zd d (b - b')) : Zd d (a * b - a' * b') := by sorry
