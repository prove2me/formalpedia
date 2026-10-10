-- Prove2me | Theorems.Thm_BookProof_HermiteBandHigher_Band_compGen
-- name    : BookProof.HermiteBandHigher.Band.compGen
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:01:42.739004+00:00
-- url     : https://prove2.me/theorems/fc2b07a9-6136-458b-a087-544bb770d998
-- title:
--   `BookProof.HermiteBandHigher.Band.compGen` {T U : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ} {r₁ r₂ M₁ M₂ m₁ m₂ : ℕ} {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁)...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHermiteBandCalculusHigher`.
--
--   `BookProof.HermiteBandHigher.Band.compGen` {T U : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ} {r₁ r₂ M₁ M₂ m₁ m₂ : ℕ} {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hT : Band T r₁ M₁ C₁ (gpow m₁)) (hU : Band U r₂ M₂ C₂ (gpow m₂)) : Band (U ∘ₗ T) (r₁ + r₂) (M₁ * M₂) (M₁ * C₁ * C₂ * Real.sqrt ((r₁ : ℝ) + 1) ^ m₂) (gpow (m₁ + m₂))
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteBandHigher.Band.compGen`.

-- Generated from ChapterHermiteBandCalculusHigher.lean — theorem BookProof.HermiteBandHigher.Band.compGen
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

theorem BookProof.HermiteBandHigher.Band.compGen {T U : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ}
    {r₁ r₂ M₁ M₂ m₁ m₂ : ℕ} {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hT : Band T r₁ M₁ C₁ (gpow m₁)) (hU : Band U r₂ M₂ C₂ (gpow m₂)) :
    Band (U ∘ₗ T) (r₁ + r₂) (M₁ * M₂)
      (M₁ * C₁ * C₂ * Real.sqrt ((r₁ : ℝ) + 1) ^ m₂) (gpow (m₁ + m₂)) := by sorry
