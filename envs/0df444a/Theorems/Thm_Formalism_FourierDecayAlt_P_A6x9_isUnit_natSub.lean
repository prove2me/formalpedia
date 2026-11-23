-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A6x9_isUnit_natSub
-- name    : Formalism.FourierDecayAlt.P.A6x9.isUnit_natSub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:54:58.792556+00:00
-- url     : https://prove2.me/theorems/7888af02-4f26-4296-97d8-c48b086b5136
-- title:
--   A6x9: is Unit nat Sub
-- statement:
--   The A6x9 construction uses the is Unit nat Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PadicChangeOfVariables.lean#L48-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PadicChangeOfVariables.lean#L48-L56

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PadicChangeOfVariables
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x9
variable {K : Type} [CommRing K]
variable [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K} {ψ : AddChar K ℂ}

theorem Formalism.FourierDecayAlt.P.A6x9.isUnit_natSub (hn : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) (n m : ℕ) (h : n ≠ m) :
    IsUnit ((n : K) - (m : K)) := by sorry
