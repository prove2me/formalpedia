-- Prove2me | Theorems.Thm_Formalism_FG_KeyVAux_bd_subst_sub
-- name    : Formalism.FG.KeyVAux.bd_subst_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:40:37.539295+00:00
-- url     : https://prove2.me/theorems/16f0bd4f-31ef-454d-9baa-3466118a5dbf
-- title:
--   Key VAux: bd subst sub
-- statement:
--   The Key VAux construction uses the bd subst sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/FunctionalEquationSubstVector.lean#L60-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/FunctionalEquationSubstVector.lean#L60-L73

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

theorem Formalism.FG.KeyVAux.bd_subst_sub {ι : Type v} {τ : Type w} (φ : MvPowerSeries ι K)
    (A B : ι → MvPowerSeries τ K) (hA : MvPowerSeries.HasSubst A) (hB : MvPowerSeries.HasSubst B)
    {c : ℝ} (hc : 0 ≤ c)
    (H : ∀ (n : ι →₀ ℕ) d, ‖MvPowerSeries.coeff n φ‖ *
      ‖MvPowerSeries.coeff d (n.prod (fun s e => A s ^ e) - n.prod (fun s e => B s ^ e))‖ ≤ c) :
    Bd c (MvPowerSeries.subst A φ - MvPowerSeries.subst B φ) := by sorry
