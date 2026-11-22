-- Prove2me | Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_mul
-- name    : Formalism.FG.IntegralSubstitution.integral_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:17:16.312867+00:00
-- url     : https://prove2.me/theorems/4b5eba55-7c6f-4b57-a3f9-7cee7cf82b43
-- title:
--   Integral Substitution: integral mul
-- statement:
--   The Integral Substitution construction uses the integral mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/IntegralSubstVector.lean#L13-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/IntegralSubstVector.lean#L13-L20

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
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
open Formalism Formalism.FG Formalism.FG.IntegralSubstitution
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {τ : Type w}

theorem Formalism.FG.IntegralSubstitution.integral_mul {A B : MvPowerSeries τ K} (hA : IntegralMv A) (hB : IntegralMv B) :
    IntegralMv (A * B) := by sorry
