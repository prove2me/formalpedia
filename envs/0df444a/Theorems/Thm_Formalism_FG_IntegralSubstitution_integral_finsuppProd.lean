-- Prove2me | Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_finsuppProd
-- name    : Formalism.FG.IntegralSubstitution.integral_finsuppProd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:40:11.805233+00:00
-- url     : https://prove2.me/theorems/14b764d7-f5ee-4dca-9ff9-34d5381112d2
-- title:
--   Integral Substitution: integral finsupp Prod
-- statement:
--   The Integral Substitution construction uses the integral finsupp Prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/IntegralSubstVector.lean#L34-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/IntegralSubstVector.lean#L34-L39

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

theorem Formalism.FG.IntegralSubstitution.integral_finsuppProd {ι : Type v} (a : ι → MvPowerSeries τ K) (ha : ∀ i, IntegralMv (a i))
    (n : ι →₀ ℕ) : IntegralMv (n.prod fun s e => (a s) ^ e) := by sorry
