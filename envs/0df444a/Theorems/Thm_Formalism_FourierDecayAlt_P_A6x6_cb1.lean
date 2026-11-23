-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_cb1
-- name    : Formalism.FourierDecayAlt.P.A6x6.cb1
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:51:53.324879+00:00
-- url     : https://prove2.me/theorems/d04d3a32-5af2-4435-8587-a3f215dd1492
-- title:
--   A6x6: cb1
-- statement:
--   The A6x6 construction uses the cb1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussSumModulusOfLattice.lean#L303-L306
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussSumModulusOfLattice.lean#L303-L306

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussSumModulusOfLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A6x6
open Formalism.FourierDecayAlt.P.A5x5
variable {K : Type} [CommRing K] {m : ℕ} (ψ : AddChar K ℂ)
variable {M : Matrix (Fin m) (Fin m) K}
variable {L Λ : AddSubgroup K}
variable {ψ}

theorem Formalism.FourierDecayAlt.P.A6x6.cb1 (h2 : IsUnit (2 : K)) (hM : M.IsSymm) (hInv : LatInvN Λ (gaussF ψ L M))
    {x x' u : Fin m → K} (hu : u ∈ PL L m) (hl : x - x' ∈ PL Λ m) :
    ψ (x ⬝ᵥ M *ᵥ u) = ψ (x' ⬝ᵥ M *ᵥ u) := by sorry
