-- Prove2me | Theorems.Thm_Formalism_FG_IntegralSubstitution_integralSubstV
-- name    : Formalism.FG.IntegralSubstitution.integralSubstV
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:10:03.994957+00:00
-- url     : https://prove2.me/theorems/7eb00e4e-9e6b-48f0-9c25-5b889c479c2d
-- title:
--   Integral Substitution: integral Subst V
-- statement:
--   The Integral Substitution construction uses the integral Subst V property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/IntegralSubstVector.lean#L41-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/IntegralSubstVector.lean#L41-L52

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

theorem Formalism.FG.IntegralSubstitution.integralSubstV {ι : Type v} [Finite ι] (g : MvPowerSeries ι K)
    (a : ι → MvPowerSeries τ K) (hg : IntegralMv g)
    (ha0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (ha : ∀ i, IntegralMv (a i)) :
    IntegralMv (MvPowerSeries.subst a g) := by sorry
