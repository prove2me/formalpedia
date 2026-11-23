-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveSemidefiniteClosure_finite_cosets
-- name    : Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure.finite_cosets
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:07:28.814111+00:00
-- url     : https://prove2.me/theorems/ceb92518-833c-411d-ace5-b519180506f2
-- title:
--   Positive Semidefinite Closure: finite cosets
-- statement:
--   The Positive Semidefinite Closure construction uses the finite cosets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AveragedVectorChoices.lean#L53-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AveragedVectorChoices.lean#L53-L61

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

theorem Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure.finite_cosets {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    (Λ : AddSubgroup K) (hΛ : IsOpen (Λ : Set K)) (C : Set K) (hC : IsCompact C) :
    {y : K ⧸ Λ | (Quotient.out y : K) ∈ C}.Finite := by sorry
