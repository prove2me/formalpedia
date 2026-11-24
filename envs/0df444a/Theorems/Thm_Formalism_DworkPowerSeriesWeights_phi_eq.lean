-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_phi_eq
-- name    : Formalism.DworkPowerSeriesWeights.phi_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:52:37.028167+00:00
-- url     : https://prove2.me/theorems/c42e0745-b0e9-4863-9395-8fc6e2455d42
-- title:
--   Dwork Power Series Weights: phi eq
-- statement:
--   The Dwork Power Series Weights construction uses the phi eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FirstRowMinorDegreeLeOne.lean#L346-L356
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FirstRowMinorDegreeLeOne.lean#L346-L356

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

theorem Formalism.DworkPowerSeriesWeights.phi_eq [Fintype H] [DecidableEq H] {N1 : ℕ} (x : Bool × H → Matrix (Fin N0) (Fin N0) K)
    (τ : Bool × H) (k : Fin N0) (b : Fin N1) :
    (∑ z, C (bA x (bE H N0 N1 (τ, k, b)) z) * X z :
      MvPolynomial ((Bool × H) × Fin N0 × Fin N1) K) =
      ∑ a, C (bM x τ k a) * X (τ, a, b) := by sorry
