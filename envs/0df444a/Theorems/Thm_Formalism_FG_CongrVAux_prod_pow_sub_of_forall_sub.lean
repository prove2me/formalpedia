-- Prove2me | Theorems.Thm_Formalism_FG_CongrVAux_prod_pow_sub_of_forall_sub
-- name    : Formalism.FG.CongrVAux.prod_pow_sub_of_forall_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:37:23.880645+00:00
-- url     : https://prove2.me/theorems/a891a055-a81f-44ff-9c2b-d0dd02ee06a5
-- title:
--   Congr VAux: prod pow sub of forall sub
-- statement:
--   The Congr VAux construction uses the prod pow sub of forall sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/CongrV.lean#L41-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/CongrV.lean#L41-L51

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

theorem Formalism.FG.CongrVAux.prod_pow_sub_of_forall_sub {ι : Type v} {d : τ →₀ ℕ} {k k' : ι → MvPowerSeries τ R}
    (hkk : ∀ i, Zd d (k i - k' i)) (e : ι →₀ ℕ) : Zd d (P k e - P k' e) := by sorry
