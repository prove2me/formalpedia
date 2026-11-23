-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_inv_mem
-- name    : Formalism.FourierDecayAlt.P.A6x6.inv_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:52:08.600196+00:00
-- url     : https://prove2.me/theorems/1cd030f9-7942-4cba-8cda-f7a7f2769c01
-- title:
--   A6x6: inv mem
-- statement:
--   The A6x6 construction uses the inv mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussSumModulusOfLattice.lean#L320-L327
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussSumModulusOfLattice.lean#L320-L327

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

theorem Formalism.FourierDecayAlt.P.A6x6.inv_mem (h2 : IsUnit (2 : K)) (hM : M.IsSymm) (hAdm : GaussAdm ψ L M) {u : Fin m → K}
    (hu : u ∈ PL (perp ψ L) m) : M⁻¹ *ᵥ u ∈ PL (perp ψ (perp ψ L)) m := by sorry
