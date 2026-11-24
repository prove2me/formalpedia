-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_beta_change
-- name    : Formalism.DworkPowerSeriesWeights.beta_change
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:53:28.848323+00:00
-- url     : https://prove2.me/theorems/f92f3fac-737f-43e3-abc4-12daec92e346
-- title:
--   Dwork Power Series Weights: beta change
-- statement:
--   The Dwork Power Series Weights construction uses the beta change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FirstRowMinorDegreeLeOne.lean#L381-L411
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FirstRowMinorDegreeLeOne.lean#L381-L411

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
variable {K : Type u} [Field K] {H : Type} {N0 : ℕ}

theorem Formalism.DworkPowerSeriesWeights.beta_change [Fintype H] [DecidableEq H] {N1 : ℕ}
    (x : Bool × H → Matrix (Fin N0) (Fin N0) K) (hx : ∀ τ, (x τ).det ≠ 0) (u : H → K) :
    MvPowerSeries.subst (fun z : (Bool × H) × Fin N0 × Fin N1 =>
        (∑ y, MvPowerSeries.C (bA x y z) * MvPowerSeries.X y :
          MvPowerSeries (Bool × H × Fin N0 × Fin N1) K))
      (∑ t : H, ∑ ab : Fin N0 × Fin N1, MvPowerSeries.C (u t) *
        MvPowerSeries.X ((false, t), ab.1, ab.2) * MvPowerSeries.X ((true, t), ab.1, ab.2)) =
      ∑ i : H × Fin N0 × Fin N1, MvPowerSeries.C (u i.1) * MvPowerSeries.X (false, i) *
        MvPowerSeries.X (true, i) := by sorry
