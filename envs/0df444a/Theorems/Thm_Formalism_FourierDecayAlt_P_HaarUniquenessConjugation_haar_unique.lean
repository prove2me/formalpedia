-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HaarUniquenessConjugation_haar_unique
-- name    : Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.haar_unique
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T16:16:43.550683+00:00
-- url     : https://prove2.me/theorems/09885661-9f94-4c1d-a122-bbe2afdd5b1c
-- title:
--   Haar Uniqueness Conjugation: haar unique
-- statement:
--   The Haar Uniqueness Conjugation construction uses the haar unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HaarUniquenessConjugation.lean#L120-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HaarUniquenessConjugation.lean#L120-L162

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

theorem Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.haar_unique (hE : UJEmb) (hC : UHConj) (hP : IsUnit P.det) (hH : Pᴴ * Jm ε * P = Hpk k r)
    (ν : Measure (Mt k r)) (hν : IsHaarOn (GV k r) ν) : ∃ c : ℝ≥0, ν = c • (muG ε).map (phi ε P) := by sorry
