-- Prove2me | Theorems.Thm_BookProof_HermiteBandHigher_IsBandDeg_comp
-- name    : BookProof.HermiteBandHigher.IsBandDeg.comp
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T12:03:37.208189+00:00
-- url     : https://prove2.me/theorems/b487ef39-ab4c-41ec-9356-936454f78f98
-- title:
--   `BookProof.HermiteBandHigher.IsBandDeg.comp` {m₁ m₂ : ℕ} {T U : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ} (hU : IsBandDeg m₂ U) (hT : IsBandDeg m₁ T) : IsBandDeg...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHermiteBandCalculusHigher`.
--
--   `BookProof.HermiteBandHigher.IsBandDeg.comp` {m₁ m₂ : ℕ} {T U : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ} (hU : IsBandDeg m₂ U) (hT : IsBandDeg m₁ T) : IsBandDeg (m₁ + m₂) (U ∘ₗ T)
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteBandHigher.IsBandDeg.comp`.

-- Generated from ChapterHermiteBandCalculusHigher.lean — theorem BookProof.HermiteBandHigher.IsBandDeg.comp
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteBandCalculus
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculusHigher
open BookProof.HermiteBandHigher



noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.HermiteBand BookProof.YangMillsHermite
open BookProof.NavierStokesFlow.DifferentialL2

variable {d : ℕ}

theorem BookProof.HermiteBandHigher.IsBandDeg.comp {m₁ m₂ : ℕ} {T U : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ}
    (hU : IsBandDeg m₂ U) (hT : IsBandDeg m₁ T) : IsBandDeg (m₁ + m₂) (U ∘ₗ T) := by sorry
