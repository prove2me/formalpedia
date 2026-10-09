-- Prove2me | Theorems.Thm_BookProof_GaussCoordCombo_gaussInt_leibniz_prime
-- name    : BookProof.GaussCoordCombo.gaussInt_leibniz_prime
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T12:18:58.773576+00:00
-- url     : https://prove2.me/theorems/860b6290-d339-43ff-8d39-4366789b73a3
-- title:
--   BookProof.GaussCoordCombo.gaussInt_leibniz'
-- statement:
--   BookProof.GaussCoordCombo.gaussInt_leibniz'

-- Generated from ChapterGaussCoordCombo.lean — theorem BookProof.GaussCoordCombo.gaussInt_leibniz'
import Mathlib
import Definitions.Def_ChapterGaussCoordCombo
import Definitions.Def_ChapterHermiteProductCore
open BookProof.HermiteProductCore
open BookProof.GaussCoordCombo



open MvPolynomial BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

theorem BookProof.GaussCoordCombo.gaussInt_leibniz_prime (i : Fin d) (P Q : MvPolynomial (Fin d) ℂ) :
    gaussInt (pderiv i P * Q) + gaussInt (P * pderiv i Q) = gaussInt (X i * (P * Q)) := by sorry
