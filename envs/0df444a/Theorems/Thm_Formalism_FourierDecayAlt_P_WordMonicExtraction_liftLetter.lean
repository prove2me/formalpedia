-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WordMonicExtraction_liftLetter
-- name    : Formalism.FourierDecayAlt.P.WordMonicExtraction.liftLetter
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:55:02.319383+00:00
-- url     : https://prove2.me/theorems/5201d7e8-938c-4539-8901-dc383813c91c
-- title:
--   Word Monic Extraction: lift Letter
-- statement:
--   The Word Monic Extraction construction uses the lift Letter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WordMonicExtraction.lean#L205-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WordMonicExtraction.lean#L205-L246

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordMonicExtraction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WordMonicExtraction
open Finset Polynomial Formalism.FourierDecayAlt.F7
variable {R M : Type} [Ring R] [Algebra ℂ R] [AddCommGroup M] [Module ℂ M] [Module R M]
  [IsScalarTower ℂ R M]

theorem Formalism.FourierDecayAlt.P.WordMonicExtraction.liftLetter (Ξ : Sesq M) (n s : ℕ) (D : Dat R) (A₀ A₀v : R[X]) (e t t' : ℂ) (x x' : M)
    (hs : D.s = 0) (he : e = 1 ∨ e = -1)
    (hA : D.A.Monic) (hAn : D.A.natDegree = n + s) (hAv : D.Av.Monic) (hAvn : D.Av.natDegree = n + s)
    (hA₀ : A₀.Monic) (hA₀n : A₀.natDegree = n) (hA₀v : A₀v.Monic) (hA₀vn : A₀v.natDegree = n)
    (hB : ∀ Y Y' : ℝ, Ξ (evR D.B Y • x) (evR D.Av Y' • x') =
      Ξ ((e * t⁻¹) • evR A₀ Y • x) (evR D.Av Y' • x'))
    (hBv : ∀ Y Y' : ℝ, Ξ (evR D.A Y • x) (evR D.Bv Y' • x') =
      Ξ (evR D.A Y • x) ((e * (starRingEnd ℂ t')⁻¹) • evR A₀v Y' • x')) :
    IsTopCoeff (fun Y => letterVal Ξ D Y x x') (2 * n + s) (e * (1 / t - 1 / t') * Ξ x x') := by sorry
