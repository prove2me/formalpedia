-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_EGauss_struct
-- name    : Formalism.InvariantFactorPaths.G7.EGauss.struct
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:54:49.378246+00:00
-- url     : https://prove2.me/theorems/e5c33640-41d6-49c4-9a70-2f7fabb72b93
-- title:
--   EGauss: struct
-- statement:
--   The EGauss construction uses the struct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EGauss.lean#L111-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EGauss.lean#L111-L246

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
variable {K : Type} [Field K] {ν r0 r1 : ℕ} [NeZero ν]

theorem Formalism.InvariantFactorPaths.G7.EGauss.struct (TT : Finset (ZMod (2 * ν))) (colN : ZMod (2 * ν) → ℕ)
    (hts : ∀ s, Fin (colN s) → ℕ) (hp : ∀ s c, hts s c ≤ r0) (I : ∀ s c, Fin (hts s c) → Fin r1)
    (Y : ZMod (2 * ν) × Fin r0 × Fin r0 → K) :
    ∃ (C : ℕ) (ξ : ZMod (2 * ν) → Fin r0 → K) (e : TpV ν r1 → ℕ) (l : Fin C → ℕ)
      (sf : Fin C → ZMod (2 * ν)) (T : ∀ c, Fin (l c) → Fin r0 → K)
      (I' : ∀ c, Fin (l c) → Fin r1),
      (∏ s : ZMod (2 * ν), minorProd
        (fun (i : Fin r0) (b : Fin r1) =>
          (∑ a : Fin r0, MvPolynomial.C (Y (s, i, a)) * MvPolynomial.X (s, a, b) :
            MvPolynomial (ZV ν r0 r1) K)) (hts s) (hp s) (I s)) = entryOp ξ e l sf T I' ∧
      (∀ s a, ∃ y, ξ s a = Y y) ∧ (∀ c i a, ∃ y, T c i a = Y y) ∧
      alN e = alG TT colN hts ∧ capN sf = capG TT colN hts ∧ lsN l sf = lsG TT colN hts ∧
      ∀ (J : Finset (Fin r1)) (i : ℕ), 1 ≤ i →
        (∑ x : TpV ν r1, (if (x.1.val % 2 = 0 ∧ x.2 ∉ J) ∨ (x.1.val % 2 = 1 ∧ x.2 ∈ J)
            then e x else 0) +
          ∑ c, (if (sf c).val % 2 = 1 then ((univ.image (I' c)) ∩ J).card else 0)) ≤
        ∑ s : ZMod (2 * ν), ∑ c : Fin (colN s),
          (if s.val % 2 = 0 then min (hts s c) i - ((univ.image (I s c)) ∩ J).card
          else ((univ.image (I s c)) ∩ J).card) := by sorry
