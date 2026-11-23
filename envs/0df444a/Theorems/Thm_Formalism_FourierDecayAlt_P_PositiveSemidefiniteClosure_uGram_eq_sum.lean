-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveSemidefiniteClosure_uGram_eq_sum
-- name    : Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure.uGram_eq_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:35:50.609434+00:00
-- url     : https://prove2.me/theorems/f684e2b2-9916-4c87-83f2-0d6919483b0e
-- title:
--   Positive Semidefinite Closure: u Gram eq sum
-- statement:
--   The Positive Semidefinite Closure construction uses the u Gram eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AveragedVectorChoices.lean#L79-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AveragedVectorChoices.lean#L79-L95

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AveragedVectorChoices
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure
open Classical

theorem Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure.uGram_eq_sum {K : Type} [CommRing K] (R : Subring K) (ψ : AddChar K ℂ) (m : ℕ)
    (cr : K ⧸ R.toAddSubgroup → Kˣ) (S : Set K) (h h' : Point K) (t t' : Kˣ)
    (T : Finset (K ⧸ R.toAddSubgroup))
    (hT : ∀ x, x ∉ T → Kp R ψ (pt2 h m t (cr x)) (pt2 h' m t' (cr x)) = 0) :
    uGram R ψ m cr S h h' t t' =
      ((modK R ((t : K) * (t' : K)) ^ (m * (m + 1) / 2) : ℝ) : ℂ) *
        ∑ x ∈ T.filter (fun x => (cr x : K) ∈ S),
          Kp R ψ (pt2 h m t (cr x)) (pt2 h' m t' (cr x)) := by sorry
