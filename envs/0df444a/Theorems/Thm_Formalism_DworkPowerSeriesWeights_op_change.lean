-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_op_change
-- name    : Formalism.DworkPowerSeriesWeights.op_change
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:53:33.450709+00:00
-- url     : https://prove2.me/theorems/cddff1cb-5ecc-4095-a3da-acff1ddc7067
-- title:
--   Dwork Power Series Weights: op change
-- statement:
--   The Dwork Power Series Weights construction uses the op change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FirstRowMinorDegreeLeOne.lean#L358-L379
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FirstRowMinorDegreeLeOne.lean#L358-L379

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

theorem Formalism.DworkPowerSeriesWeights.op_change [Fintype H] [DecidableEq H] {N1 : ℕ} (x : Bool × H → Matrix (Fin N0) (Fin N0) K)
    (hx : ∀ τ, (x τ).det ≠ 0) (colN : Bool × H → ℕ) (p : ∀ τ, Fin (colN τ) → ℕ)
    (hp : ∀ τ c, p τ c ≤ N0) (I : ∀ τ c, Fin (p τ c) → Fin N1) :
    (∏ τ : Bool × H, minorProd
        (fun (i : Fin N0) (b : Fin N1) => (∑ a, C (x τ i a) * X (τ, a, b) :
          MvPolynomial ((Bool × H) × Fin N0 × Fin N1) K)) (p τ) (hp τ) (I τ)) =
      aeval (fun y : Bool × H × Fin N0 × Fin N1 =>
          (∑ z, C (bA x y z) * X z : MvPolynomial ((Bool × H) × Fin N0 × Fin N1) K))
        (∏ τ : Bool × H, rename (fun y => bE H N0 N1 (τ, y))
          (minorProd (oldRowLow (N1 := N1) (bT x τ)) (p τ) (hp τ) (I τ))) := by sorry
