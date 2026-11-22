-- Prove2me | Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_pow
-- name    : Formalism.FG.IntegralSubstitution.integral_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:17:19.693809+00:00
-- url     : https://prove2.me/theorems/a6eb2a2c-f573-4b64-ace7-fc5311f26efe
-- title:
--   Integral Substitution: integral pow
-- statement:
--   The Integral Substitution construction uses the integral pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/IntegralSubstVector.lean#L28-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/IntegralSubstVector.lean#L28-L32

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

theorem Formalism.FG.IntegralSubstitution.integral_pow {A : MvPowerSeries τ K} (hA : IntegralMv A) (n : ℕ) :
    IntegralMv (A ^ n) := by sorry
