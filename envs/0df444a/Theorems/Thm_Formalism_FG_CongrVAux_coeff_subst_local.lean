-- Prove2me | Theorems.Thm_Formalism_FG_CongrVAux_coeff_subst_local
-- name    : Formalism.FG.CongrVAux.coeff_subst_local
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:36:53.404179+00:00
-- url     : https://prove2.me/theorems/ce977279-9259-4ee2-9cc1-4c9790646708
-- title:
--   Congr VAux: coeff subst local
-- statement:
--   The Congr VAux construction uses the coeff subst local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/CongrV.lean#L53-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/CongrV.lean#L53-L63

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

theorem Formalism.FG.CongrVAux.coeff_subst_local {ι : Type v} [Finite ι] {d : τ →₀ ℕ} {k k' : ι → MvPowerSeries τ R}
    (hk : ∀ i, constantCoeff (k i) = 0) (hk' : ∀ i, constantCoeff (k' i) = 0)
    (hkk : ∀ i, ∀ e ≤ d, coeff e (k i) = coeff e (k' i)) (g : MvPowerSeries ι R) :
    coeff d (subst k g) = coeff d (subst k' g) := by sorry
