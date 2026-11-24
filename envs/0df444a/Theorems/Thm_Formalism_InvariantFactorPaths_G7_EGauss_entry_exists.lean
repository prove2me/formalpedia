-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_EGauss_entry_exists
-- name    : Formalism.InvariantFactorPaths.G7.EGauss.entry_exists
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:54:36.560826+00:00
-- url     : https://prove2.me/theorems/5ee0d9d5-52ce-482e-b37e-e5afc5bd5f4e
-- title:
--   EGauss: entry exists
-- statement:
--   The EGauss construction uses the entry exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EGauss.lean#L64-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EGauss.lean#L64-L92

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementG
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_GField
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FJEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Labels
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_KOneConsequence
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EGauss
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
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral frameJet jetPair minorProd)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)
open Formalism.InvariantFactorPaths.G7.EGauss
variable {K : Type} [Field K] {ν r0 r1 : ℕ}

theorem Formalism.InvariantFactorPaths.G7.EGauss.entry_exists [NeZero ν] {At Al : Type} [Fintype At] [Fintype Al]
    (ξ : ZMod (2 * ν) → Fin r0 → K) (g : At → TpV ν r1) (pos : Al → ZMod (2 * ν)) (ht : Al → ℕ)
    (Tm : ∀ x, Fin (ht x) → Fin r0 → K) (Ic : ∀ x, Fin (ht x) → Fin r1) :
    ∃ (C : ℕ) (e : TpV ν r1 → ℕ) (l : Fin C → ℕ) (sf : Fin C → ZMod (2 * ν))
      (T : ∀ c, Fin (l c) → Fin r0 → K) (I : ∀ c, Fin (l c) → Fin r1),
      (∏ x, topForm ξ (g x)) * ∏ x, minorAt (pos x) (Tm x) (Ic x) = entryOp ξ e l sf T I ∧
      (∀ f : TpV ν r1 → ℕ, ∑ y, f y * e y = ∑ x, f (g x)) ∧
      (∀ f : ZMod (2 * ν) → (h : ℕ) → (Fin h → Fin r1) → ℕ,
        ∑ c, f (sf c) (l c) (I c) = ∑ x, f (pos x) (ht x) (Ic x)) ∧
      (∀ c i a, ∃ x i', T c i a = Tm x i' a) := by sorry
