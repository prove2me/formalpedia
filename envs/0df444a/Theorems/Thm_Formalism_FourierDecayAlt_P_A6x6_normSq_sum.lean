-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_normSq_sum
-- name    : Formalism.FourierDecayAlt.P.A6x6.normSq_sum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:52:13.168037+00:00
-- url     : https://prove2.me/theorems/198f8b85-ce13-4562-8ce8-eef0b190de19
-- title:
--   A6x6: norm Sq sum
-- statement:
--   The A6x6 construction uses the norm Sq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussSumModulusOfLattice.lean#L329-L405
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussSumModulusOfLattice.lean#L329-L405

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

theorem Formalism.FourierDecayAlt.P.A6x6.normSq_sum (h2 : IsUnit (2 : K)) (hM : M.IsSymm) (hInv : LatInvN Λ (gaussF ψ L M))
    (hu : ∀ x : K, conj (ψ x) = ψ (-x)) (hdet : IsUnit M.det)
    (hAdm : GaussAdm ψ L M) (hPP : perp ψ (perp ψ L) = L)
    (hfin : (PL Λ m).relIndex (PL L m) ≠ 0) :
    (∑ᶠ y : Fin m → K ⧸ Λ, gaussF ψ L M (sec Λ y)) *
        conj (∑ᶠ y : Fin m → K ⧸ Λ, gaussF ψ L M (sec Λ y)) =
      ((PL Λ m).relIndex (PL L m) : ℂ) *
        ((PL Λ m).relIndex ((PL (perp ψ L) m).map (mv M⁻¹)) : ℂ) := by sorry
