-- Prove2me | Theorems.Thm_BookProof_GaussCoordCombo_gaussInt_sub_prime
-- name    : BookProof.GaussCoordCombo.gaussInt_sub_prime
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T12:19:17.833985+00:00
-- url     : https://prove2.me/theorems/968d4328-a6b3-4ec5-b89d-43fd2387bec8
-- title:
--   BookProof.GaussCoordCombo.gaussInt_sub'
-- statement:
--   BookProof.GaussCoordCombo.gaussInt_sub'

-- Generated from ChapterGaussCoordCombo.lean — theorem BookProof.GaussCoordCombo.gaussInt_sub'
import Mathlib
import Definitions.Def_ChapterGaussCoordCombo
import Definitions.Def_ChapterHermiteProductCore
open BookProof.HermiteProductCore
open BookProof.GaussCoordCombo



open MvPolynomial BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

theorem BookProof.GaussCoordCombo.gaussInt_sub_prime (r s : MvPolynomial (Fin d) ℂ) :
    gaussInt (r - s) = gaussInt r - gaussInt s := by sorry
