-- Prove2me | Theorems.Thm_BookProof_HermiteBandHigher_IsBandDeg_sum
-- name    : BookProof.HermiteBandHigher.IsBandDeg.sum
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T12:03:19.104693+00:00
-- url     : https://prove2.me/theorems/b35bf2e8-a21c-4ca8-b16d-396119a0ce0b
-- title:
--   `BookProof.HermiteBandHigher.IsBandDeg.sum` {m : ℕ} {ι : Type*} (s : Finset ι) (F : ι → MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ) (h : ∀ i ∈ s, IsBandDeg m (F i))...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHermiteBandCalculusHigher`.
--
--   `BookProof.HermiteBandHigher.IsBandDeg.sum` {m : ℕ} {ι : Type*} (s : Finset ι) (F : ι → MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ) (h : ∀ i ∈ s, IsBandDeg m (F i)) : IsBandDeg m (∑ i ∈ s, F i)
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteBandHigher.IsBandDeg.sum`.

-- Generated from ChapterHermiteBandCalculusHigher.lean — theorem BookProof.HermiteBandHigher.IsBandDeg.sum
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteBandCalculus
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculusHigher
import Definitions.Def_ChapterSirkFinitePrecision
open BookProof.SirkFinitePrecision
open BookProof.SirkFinitePrecision.CertInterval
open BookProof.HermiteBandHigher



noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.HermiteBand BookProof.YangMillsHermite
open BookProof.NavierStokesFlow.DifferentialL2

variable {d : ℕ}

theorem BookProof.HermiteBandHigher.IsBandDeg.sum {m : ℕ} {ι : Type*} (s : Finset ι)
    (F : ι → MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ)
    (h : ∀ i ∈ s, IsBandDeg m (F i)) : IsBandDeg m (∑ i ∈ s, F i) := by sorry
