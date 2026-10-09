-- Prove2me | Theorems.Thm_BookProof_DensitySpectral_density_spectral
-- name    : BookProof.DensitySpectral.density_spectral
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T22:56:44.441816+00:00
-- url     : https://prove2.me/theorems/2fa9f786-dc2a-43c0-93bc-56cd51b44179
-- title:
--   `BookProof.DensitySpectral.density_spectral` {ρ : Matrix n n ℂ} (h : IsDensityMatrix ρ) : ρ = (h.1.eigenvectorUnitary : Matrix n n ℂ) * diagonal (RCLike.ofReal ∘ h.1.eigenvalues) *
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDensitySpectral`.
--
--   `BookProof.DensitySpectral.density_spectral` {ρ : Matrix n n ℂ} (h : IsDensityMatrix ρ) : ρ = (h.1.eigenvectorUnitary : Matrix n n ℂ) * diagonal (RCLike.ofReal ∘ h.1.eigenvalues) * (h.1.eigenvectorUnitary : Matrix n n ℂ)ᴴ
--
--   Formalization note: Lean 4 identifier `BookProof.DensitySpectral.density_spectral`.

-- Generated from ChapterDensitySpectral.lean — theorem BookProof.DensitySpectral.density_spectral
import Mathlib
import Definitions.Def_ChapterDensitySpectral
import Definitions.Def_ChapterB4
import Definitions.Def_ChapterDensityMarginalConditional
open BookProof.ChapterB4
open BookProof.DensitySpectral



open Matrix
open scoped BigOperators ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem BookProof.DensitySpectral.density_spectral {ρ : Matrix n n ℂ} (h : IsDensityMatrix ρ) :
    ρ = (h.1.eigenvectorUnitary : Matrix n n ℂ)
        * diagonal (RCLike.ofReal ∘ h.1.eigenvalues)
        * (h.1.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by sorry
