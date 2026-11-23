-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveSemidefiniteClosure_intLat_eq_sum
-- name    : Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure.intLat_eq_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:31:29.898522+00:00
-- url     : https://prove2.me/theorems/fd4e1b52-bc11-461a-8984-51d8dfb9cd23
-- title:
--   Positive Semidefinite Closure: int Lat eq sum
-- statement:
--   The Positive Semidefinite Closure construction uses the int Lat eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AveragedVectorChoices.lean#L310-L324
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AveragedVectorChoices.lean#L310-L324

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

theorem Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure.intLat_eq_sum {K : Type} [CommRing K] (R : Subring K) (Λ : AddSubgroup K) (Om : Set K)
    (hfin : {y : K ⧸ Λ | (Quotient.out y : K) ∈ Om}.Finite) (g : K → ℂ) :
    intLat R Λ Om g = (volL R Λ : ℂ) * ∑ y ∈ hfin.toFinset, g (Quotient.out y) := by sorry
