-- Prove2me | Theorems.Thm_Formalism_FG_KeyVAux_bd_prod_sub
-- name    : Formalism.FG.KeyVAux.bd_prod_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:40:35.620914+00:00
-- url     : https://prove2.me/theorems/68d2c3c5-a0d8-4580-a676-da7f471297f4
-- title:
--   Key VAux: bd prod sub
-- statement:
--   The Key VAux construction uses the bd prod sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/FunctionalEquationSubstVector.lean#L54-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/FunctionalEquationSubstVector.lean#L54-L58

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_NormSigmaLeOne
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CoeffV
import Definitions.Def_Lemmata_MultivariateIntegrals_IntegralMv
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FunctionalEquationSubstVector
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
open Formalism Formalism.FG Formalism.FG.KeyVAux
open Formalism.G Formalism.LT
variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem Formalism.FG.KeyVAux.bd_prod_sub {τ : Type w} {ι : Type v} {C : ℝ} (hC : 0 ≤ C) (X Y : ι → MvPowerSeries τ K)
    (s : Finset ι) (hX : ∀ i ∈ s, IntegralMv (X i)) (hY : ∀ i ∈ s, IntegralMv (Y i))
    (hXY : ∀ i ∈ s, Bd C (X i - Y i)) :
    Bd C (∏ i ∈ s, X i - ∏ i ∈ s, Y i) := by sorry
