-- Prove2me | Theorems.Thm_BookProof_HermiteBandHigher_IsBandR_comp
-- name    : BookProof.HermiteBandHigher.IsBandR.comp
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T12:06:58.887018+00:00
-- url     : https://prove2.me/theorems/a8e5f0b2-7b5e-40f3-a21e-5985fde1c283
-- title:
--   `BookProof.HermiteBandHigher.IsBandR.comp` {r₁ r₂ m₁ m₂ : ℕ} {T U : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ} (hU : IsBandR r₂ m₂ U) (hT : IsBandR r₁ m₁ T)...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHermiteBandCalculusHigher`.
--
--   `BookProof.HermiteBandHigher.IsBandR.comp` {r₁ r₂ m₁ m₂ : ℕ} {T U : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ} (hU : IsBandR r₂ m₂ U) (hT : IsBandR r₁ m₁ T) : IsBandR (r₁ + r₂) (m₁ + m₂) (U ∘ₗ T)
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteBandHigher.IsBandR.comp`.

-- Generated from ChapterHermiteBandCalculusHigher.lean — theorem BookProof.HermiteBandHigher.IsBandR.comp
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculusHigher
import Definitions.Def_ChapterHermiteBandCalculus
open BookProof.HermiteBand
open BookProof.HermiteBandHigher



noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.HermiteBand BookProof.YangMillsHermite
open BookProof.NavierStokesFlow.DifferentialL2

variable {d : ℕ}

theorem BookProof.HermiteBandHigher.IsBandR.comp {r₁ r₂ m₁ m₂ : ℕ}
    {T U : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ}
    (hU : IsBandR r₂ m₂ U) (hT : IsBandR r₁ m₁ T) :
    IsBandR (r₁ + r₂) (m₁ + m₂) (U ∘ₗ T) := by sorry
