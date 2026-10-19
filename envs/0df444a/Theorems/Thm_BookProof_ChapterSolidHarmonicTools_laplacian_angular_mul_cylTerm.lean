-- Prove2me | Theorems.Thm_BookProof_ChapterSolidHarmonicTools_laplacian_angular_mul_cylTerm
-- name    : BookProof.ChapterSolidHarmonicTools.laplacian_angular_mul_cylTerm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:56:15.040315+00:00
-- url     : https://prove2.me/theorems/e0bf0eea-3b77-474e-b8e6-e640a858d507
-- title:
--   `BookProof.ChapterSolidHarmonicTools.laplacian_angular_mul_cylTerm` {A : E → ℝ} {x : E} {e : E} (he : ‖e‖ = 1) {μ : ℕ} (j m : ℕ) (hA : ContDiffAt ℝ 2 A x) (hharm : (Δ A) x = 0) (he
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSolidHarmonicTools`.
--
--   `BookProof.ChapterSolidHarmonicTools.laplacian_angular_mul_cylTerm` {A : E → ℝ} {x : E} {e : E} (he : ‖e‖ = 1) {μ : ℕ} (j m : ℕ) (hA : ContDiffAt ℝ 2 A x) (hharm : (Δ A) x = 0) (heuler : fderiv ℝ A x x = μ * A x) (haxis : fderiv ℝ A x e = 0) : (Δ fun y : E => A y * ((⟪e, y⟫_ℝ) ^ j * (‖y‖ ^ 2) ^ m)) x = A x * ((j : ℝ) * ((j : ℝ) - 1) * (⟪e, x⟫_ℝ) ^ (j - 2) * (‖x‖ ^ 2) ^ m + (4 * m * ((m : ℝ) - 1) + 2 * (Module.finrank ℝ E) * m + 4 * j * m + 4 * μ * m) * (⟪e, x⟫_ℝ) ^ j * (‖x‖ ^ 2) ^ (m - 1))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSolidHarmonicTools.laplacian_angular_mul_cylTerm`.

-- Generated from ChapterSolidHarmonicTools.lean — theorem BookProof.ChapterSolidHarmonicTools.laplacian_angular_mul_cylTerm
import Definitions.Def_ChapterLaplacianProduct
import Mathlib
import Definitions.Def_ChapterSolidHarmonicTools
import Definitions.Def_ChapterRadialLaplacian
open BookProof.ChapterRadialLaplacian
open BookProof.ChapterSolidHarmonicTools



open Laplacian InnerProductSpace BookProof.ChapterRadialLaplacian
open BookProof.ChapterLaplacianProduct
open scoped RealInnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem BookProof.ChapterSolidHarmonicTools.laplacian_angular_mul_cylTerm {A : E → ℝ} {x : E} {e : E} (he : ‖e‖ = 1) {μ : ℕ}
    (j m : ℕ) (hA : ContDiffAt ℝ 2 A x) (hharm : (Δ A) x = 0)
    (heuler : fderiv ℝ A x x = μ * A x) (haxis : fderiv ℝ A x e = 0) :
    (Δ fun y : E => A y * ((⟪e, y⟫_ℝ) ^ j * (‖y‖ ^ 2) ^ m)) x
      = A x * ((j : ℝ) * ((j : ℝ) - 1) * (⟪e, x⟫_ℝ) ^ (j - 2) * (‖x‖ ^ 2) ^ m
        + (4 * m * ((m : ℝ) - 1) + 2 * (Module.finrank ℝ E) * m + 4 * j * m + 4 * μ * m)
            * (⟪e, x⟫_ℝ) ^ j * (‖x‖ ^ 2) ^ (m - 1)) := by sorry
