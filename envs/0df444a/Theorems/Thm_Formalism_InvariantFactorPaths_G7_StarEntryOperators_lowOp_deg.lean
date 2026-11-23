-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_StarEntryOperators_lowOp_deg
-- name    : Formalism.InvariantFactorPaths.G7.StarEntryOperators.lowOp_deg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:56:04.121519+00:00
-- url     : https://prove2.me/theorems/93c0bc28-aa2e-4ad4-8bfa-a4ac00ecfd07
-- title:
--   Star Entry Operators: low Op deg
-- statement:
--   The Star Entry Operators construction uses the low Op deg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NormLeOfDvd.lean#L42-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NormLeOfDvd.lean#L42-L49

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NormLeOfDvd
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
open Formalism.DworkPowerSeriesWeights (Integral jetPair mfact opInt)
open Formalism.GrowthSums (gamP rhoP)
open Formalism.InvariantFactorPaths.G7.StarEntryOperators

theorem Formalism.InvariantFactorPaths.G7.StarEntryOperators.lowOp_deg {K : Type} [Field K] (hM : MinorProdDegree) {ν r0 r1 C : ℕ} [NeZero ν]
    (l : Fin C → ℕ) (sf : Fin C → ZMod (2 * ν)) (T : ∀ c, Fin (l c) → Fin r0 → K)
    (I : ∀ c, Fin (l c) → Fin r1) (n : ZV ν r0 r1 →₀ ℕ) (hn : n ∈ (lowOp l sf T I).support) :
    (∀ s, ∑ x : Fin r0 × Fin r1, n (s, x) = lsN l sf s) ∧ n.degree = ∑ s, lsN l sf s := by sorry
