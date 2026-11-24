-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_count_pred
-- name    : Formalism.DworkPowerSeriesWeights.count_pred
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:54:21.16139+00:00
-- url     : https://prove2.me/theorems/bc678d52-b38b-4300-aa48-e475bf8a5e8f
-- title:
--   Dwork Power Series Weights: count pred
-- statement:
--   The Dwork Power Series Weights construction uses the count pred property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FirstRowMinorDegreeLeOne.lean#L93-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FirstRowMinorDegreeLeOne.lean#L93-L107

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormDetLeOneOfEntries
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_MfactEqProdUniv
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FirstRowMinorDegreeLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open MvPolynomial

theorem Formalism.DworkPowerSeriesWeights.count_pred {J : Type} [Fintype J] [DecidableEq J] {N1 p : ℕ} (τ : Fin p → J)
    (I : Fin p → Fin N1) (Pr : J → Prop) [DecidablePred Pr] :
    (∑ y ∈ Finset.univ.filter (fun y : J × Fin N1 => Pr y.1),
      (∑ i, Finsupp.single (τ i, I i) 1 : J × Fin N1 →₀ ℕ) y) =
      (Finset.univ.filter (fun i => Pr (τ i))).card := by sorry
