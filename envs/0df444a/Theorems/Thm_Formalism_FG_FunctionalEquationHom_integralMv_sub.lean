-- Prove2me | Theorems.Thm_Formalism_FG_FunctionalEquationHom_integralMv_sub
-- name    : Formalism.FG.FunctionalEquationHom.integralMv_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:37:20.232199+00:00
-- url     : https://prove2.me/theorems/8344e05e-58d7-4d9f-8d1b-2ae660100bcb
-- title:
--   Functional Equation Hom: integral Mv sub
-- statement:
--   The Functional Equation Hom construction uses the integral Mv sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/FunctionalEquationHomVector.lean#L17-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/FunctionalEquationHomVector.lean#L17-L24

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CoeffExpandEqZero
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CoeffV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_InvIntV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FunctionalEquationSubstVector
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FunctionalEquationHomVector
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
open Formalism Formalism.FG Formalism.FG.FunctionalEquationHom
open Formalism.G Formalism.LT
variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem Formalism.FG.FunctionalEquationHom.integralMv_sub {τ : Type w} {a b : MvPowerSeries τ K} (ha : IntegralMv a)
    (hb : IntegralMv b) : IntegralMv (a - b) := by sorry
