-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_StarEntryOperators_aeval_entry
-- name    : Formalism.InvariantFactorPaths.G7.StarEntryOperators.aeval_entry
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:33:34.901717+00:00
-- url     : https://prove2.me/theorems/3d598bf4-0627-4978-adf4-8911ba7faeae
-- title:
--   Star Entry Operators: aeval entry
-- statement:
--   The Star Entry Operators construction uses the aeval entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NormLeOfDvd.lean#L116-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NormLeOfDvd.lean#L116-L140

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
variable {K : Type} [Field K] {ν r0 r1 : ℕ}

theorem Formalism.InvariantFactorPaths.G7.StarEntryOperators.aeval_entry [NeZero ν] {C : ℕ} (TT : Finset (ZMod (2 * ν)))
    (ξ : ZMod (2 * ν) → Fin r0 → K) (e : TpV ν r1 → ℕ) (he : ∀ x : TpV ν r1, x.1 ∉ TT → e x = 0)
    (l : Fin C → ℕ) (sf : Fin C → ZMod (2 * ν)) (T : ∀ c, Fin (l c) → Fin r0 → K)
    (I : ∀ c, Fin (l c) → Fin r1) :
    MvPolynomial.aeval (fun i : TpV ν r1 ⊕ ZV ν r0 r1 =>
        (∑ x, MvPolynomial.C (Amat TT ξ i x) * MvPolynomial.X x : MvPolynomial (ZV ν r0 r1) K))
      (topMonoP (Finsupp.equivFunOnFinite.symm e) * lowPoly (lowOp l sf T I)) =
      entryOp ξ e l sf T I := by sorry
