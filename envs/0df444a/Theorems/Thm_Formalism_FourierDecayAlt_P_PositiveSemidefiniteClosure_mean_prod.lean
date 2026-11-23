-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveSemidefiniteClosure_mean_prod
-- name    : Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure.mean_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:31:18.426465+00:00
-- url     : https://prove2.me/theorems/6962fb38-6b98-47e7-9508-1d8c2535f1e9
-- title:
--   Positive Semidefinite Closure: mean prod
-- statement:
--   The Positive Semidefinite Closure construction uses the mean prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AveragedVectorChoices.lean#L327-L344
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AveragedVectorChoices.lean#L327-L344

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

theorem Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure.mean_prod {K : Type} [CommRing K] (hCM : CharMean) (R : Subring K) (ψ : AddChar K ℂ)
    (L₁ L₂ : AddSubgroup K) (A B : Finset K) (le₁ : L₁ ≤ R.toAddSubgroup)
    (le₂ : R.toAddSubgroup ≤ L₂) (hA : IsReps A L₂ R.toAddSubgroup)
    (hB : IsReps B R.toAddSubgroup L₁) (a : K) (ha : a ∈ perp ψ L₁) :
    ((A.card : ℂ) * (B.card : ℂ))⁻¹ * ∑ p ∈ A ×ˢ B, ψ (a * (p.1 + p.2)) =
      if a ∈ perp ψ L₂ then 1 else 0 := by sorry
