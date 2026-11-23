-- Prove2me | Theorems.Thm_Formalism_FG_CongrVAux_divBy_prod_sub
-- name    : Formalism.FG.CongrVAux.divBy_prod_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:36:59.347679+00:00
-- url     : https://prove2.me/theorems/2838f77e-f109-4d1c-a912-4b4008c70ce4
-- title:
--   Congr VAux: div By prod sub
-- statement:
--   The Congr VAux construction uses the div By prod sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/CongrV.lean#L152-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/CongrV.lean#L152-L162

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

theorem Formalism.FG.CongrVAux.divBy_prod_sub {ι : Type v} {c : K} {a b : ι → MvPowerSeries τ K}
    (ha : ∀ i, IntegralMv (a i)) (hb : ∀ i, IntegralMv (b i)) (n : ι → ℕ)
    (h : ∀ i, DivByMv c (a i ^ n i - b i ^ n i)) (s : Finset ι) :
    DivByMv c (∏ i ∈ s, a i ^ n i - ∏ i ∈ s, b i ^ n i) := by sorry
