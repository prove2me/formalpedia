-- Prove2me | Theorems.Thm_Formalism_FG_KeyVAux_subst_expand
-- name    : Formalism.FG.KeyVAux.subst_expand
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:40:59.88412+00:00
-- url     : https://prove2.me/theorems/fc9766cd-a11b-4874-a7aa-8320db27114e
-- title:
--   Key VAux: subst expand
-- statement:
--   The Key VAux construction uses the subst expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/FunctionalEquationSubstVector.lean#L75-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/FunctionalEquationSubstVector.lean#L75-L83

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

theorem Formalism.FG.KeyVAux.subst_expand {ι : Type v} {τ : Type w} {R : Type u} [CommRing R] (q : ℕ) (hq : q ≠ 0)
    {a : ι → MvPowerSeries τ R} (ha : MvPowerSeries.HasSubst a) (φ : MvPowerSeries ι R) :
    MvPowerSeries.subst a (MvPowerSeries.expand q hq φ) =
      MvPowerSeries.subst (fun i => a i ^ q) φ := by sorry
