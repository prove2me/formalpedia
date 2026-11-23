-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_mem_perp_of_dot
-- name    : Formalism.FourierDecayAlt.P.A6x6.mem_perp_of_dot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:06:23.644874+00:00
-- url     : https://prove2.me/theorems/2f90df36-6819-4926-bdad-4390fba40b56
-- title:
--   A6x6: mem perp of dot
-- statement:
--   The A6x6 construction uses the mem perp of dot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussSumModulusOfLattice.lean#L227-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussSumModulusOfLattice.lean#L227-L236

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

theorem Formalism.FourierDecayAlt.P.A6x6.mem_perp_of_dot {L : AddSubgroup K} {v : Fin m → K}
    (h : ∀ x ∈ PL L m, ψ (x ⬝ᵥ v) = 1) : v ∈ PL (perp ψ L) m := by sorry
