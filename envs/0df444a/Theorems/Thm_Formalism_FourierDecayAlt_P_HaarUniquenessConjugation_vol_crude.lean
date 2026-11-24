-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HaarUniquenessConjugation_vol_crude
-- name    : Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.vol_crude
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T16:16:39.921579+00:00
-- url     : https://prove2.me/theorems/c833a374-4ec7-4635-979e-05136b2c1e1b
-- title:
--   Haar Uniqueness Conjugation: vol crude
-- statement:
--   The Haar Uniqueness Conjugation construction uses the vol crude property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HaarUniquenessConjugation.lean#L174-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HaarUniquenessConjugation.lean#L174-L221

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LiftErrorLocal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HaarUniquenessConjugation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HaarUniquenessConjugation
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
variable {ε : Fin (2 * r + k + 1) → Bool} {P : Mat k r}

theorem Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.vol_crude (hE : UJEmb) (hV : VolGrowth) (hC : UHConj) (hP : IsUnit P.det) (hH : Pᴴ * Jm ε * P = Hpk k r)
    (ν : Measure (Mt k r)) (hν : IsHaarOn (GV k r) ν) :
    ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R → ν {g | gN (Matrix.of g) ≤ R} ≤
      ENNReal.ofReal (C * R ^ (2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2)) := by sorry
