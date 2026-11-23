-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_gauss_abs
-- name    : Formalism.FourierDecayAlt.P.A6x6.gauss_abs
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:52:00.941531+00:00
-- url     : https://prove2.me/theorems/a5c8e788-3aa8-4be7-9b64-21ac3d5414fa
-- title:
--   A6x6: gauss abs
-- statement:
--   The A6x6 construction uses the gauss abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussSumModulusOfLattice.lean#L95-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussSumModulusOfLattice.lean#L95-L129

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

theorem Formalism.FourierDecayAlt.P.A6x6.gauss_abs {H : Type} [AddCommGroup H] [Fintype H] (F : H → ℂ) (B : H → H → ℂ)
    (hF : ∀ y w, F (y + w) = F y * F w * B y w)
    (hn : ∀ y, F y * conj (F y) = 1)
    (hB : ∀ w y y', B (y + y') w = B y w * B y' w)
    (hB0 : ∀ w, B 0 w = 1)
    (h1 : ∀ w, (∀ y, B y w = 1) → F w = 1) :
    (∑ y, F y) * conj (∑ y, F y) =
      (Nat.card H : ℂ) * (Nat.card {w : H // ∀ y, B y w = 1} : ℂ) := by sorry
