-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_aa_eq
-- name    : Formalism.DworkPowerSeriesWeights.aa_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:52:52.162527+00:00
-- url     : https://prove2.me/theorems/4cc52b17-b704-46a8-a977-48de331f52a3
-- title:
--   Dwork Power Series Weights: aa eq
-- statement:
--   The Dwork Power Series Weights construction uses the aa eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FirstRowMinorDegreeLeOne.lean#L334-L344
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FirstRowMinorDegreeLeOne.lean#L334-L344

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

theorem Formalism.DworkPowerSeriesWeights.aa_eq [Fintype H] [DecidableEq H] {N1 : ℕ} (x : Bool × H → Matrix (Fin N0) (Fin N0) K)
    (z : (Bool × H) × Fin N0 × Fin N1) :
    (∑ y, MvPowerSeries.C (bA x y z) * MvPowerSeries.X y :
      MvPowerSeries (Bool × H × Fin N0 × Fin N1) K) =
      ∑ i, MvPowerSeries.C (bM x z.1 i z.2.1) * MvPowerSeries.X (z.1.1, z.1.2, i, z.2.2) := by sorry
