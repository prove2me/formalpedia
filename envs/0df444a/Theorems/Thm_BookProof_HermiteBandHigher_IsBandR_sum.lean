-- Prove2me | Theorems.Thm_BookProof_HermiteBandHigher_IsBandR_sum
-- name    : BookProof.HermiteBandHigher.IsBandR.sum
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T12:03:06.18598+00:00
-- url     : https://prove2.me/theorems/d9357fdf-2885-4bcb-b185-e0625f7e95c7
-- title:
--   `BookProof.HermiteBandHigher.IsBandR.sum` {r m : ℕ} {ι : Type*} (s : Finset ι) (F : ι → MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ) (h : ∀ i ∈ s, IsBandR r m (F i))...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHermiteBandCalculusHigher`.
--
--   `BookProof.HermiteBandHigher.IsBandR.sum` {r m : ℕ} {ι : Type*} (s : Finset ι) (F : ι → MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ) (h : ∀ i ∈ s, IsBandR r m (F i)) : IsBandR r m (∑ i ∈ s, F i)
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteBandHigher.IsBandR.sum`.

-- Generated from ChapterHermiteBandCalculusHigher.lean — theorem BookProof.HermiteBandHigher.IsBandR.sum
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

theorem BookProof.HermiteBandHigher.IsBandR.sum {r m : ℕ} {ι : Type*} (s : Finset ι)
    (F : ι → MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ)
    (h : ∀ i ∈ s, IsBandR r m (F i)) : IsBandR r m (∑ i ∈ s, F i) := by sorry
