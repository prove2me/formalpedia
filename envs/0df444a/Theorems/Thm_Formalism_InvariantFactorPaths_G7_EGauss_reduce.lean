-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_EGauss_reduce
-- name    : Formalism.InvariantFactorPaths.G7.EGauss.reduce
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:53:34.65527+00:00
-- url     : https://prove2.me/theorems/f9e4a830-f94e-4597-9a6e-446647cadb8c
-- title:
--   EGauss: reduce
-- statement:
--   The EGauss construction uses the reduce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EGauss.lean#L258-L319
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EGauss.lean#L258-L319

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

theorem Formalism.InvariantFactorPaths.G7.EGauss.reduce (p : ℕ) [Fact p.Prime] (ν r0 r1 : ℕ) [NeZero ν] (u : ZMod (2 * ν) → ℂ_[p])
    (F : MvPowerSeries (ZV ν r0 r1) ℂ_[p]) (TT : Finset (ZMod (2 * ν))) (colN : ZMod (2 * ν) → ℕ)
    (hts : ∀ s, Fin (colN s) → ℕ) (hp : ∀ s c, hts s c ≤ r0) (I : ∀ s c, Fin (hts s c) → Fin r1)
    (hp2 : 2 < p) (hu : ∀ s, ‖u s‖ ≤ 1) (hF : InClass (p : ℂ_[p]) (hhS p u) F) :
    ∃ (K : Type) (_ : NormedField K), IsUltrametricDist K ∧
      ∃ (C : ℕ) (u' : ZMod (2 * ν) → K) (F' : MvPowerSeries (ZV ν r0 r1) K)
        (ξ : ZMod (2 * ν) → Fin r0 → K) (e : TpV ν r1 → ℕ) (l : Fin C → ℕ)
        (sf : Fin C → ZMod (2 * ν)) (T : ∀ c, Fin (l c) → Fin r0 → K)
        (I' : ∀ c, Fin (l c) → Fin r1),
        EntryHyp p ν r0 r1 C u' F' TT ξ e l T ∧
        (∀ n, ‖MvPolynomial.coeff n (frameJet colN hts hp I F)‖ ≤
          ‖jetPair (entryOp ξ e l sf T I') F'‖) ∧
        alN e = alG TT colN hts ∧ capN sf = capG TT colN hts ∧ lsN l sf = lsG TT colN hts ∧
        ∀ (J : Finset (Fin r1)) (i : ℕ), 1 ≤ i →
          (∑ x : TpV ν r1, (if (x.1.val % 2 = 0 ∧ x.2 ∉ J) ∨ (x.1.val % 2 = 1 ∧ x.2 ∈ J)
              then e x else 0) +
            ∑ c, (if (sf c).val % 2 = 1 then ((univ.image (I' c)) ∩ J).card else 0)) ≤
          ∑ s : ZMod (2 * ν), ∑ c : Fin (colN s),
            (if s.val % 2 = 0 then min (hts s c) i - ((univ.image (I s c)) ∩ J).card
            else ((univ.image (I s c)) ∩ J).card) := by sorry
