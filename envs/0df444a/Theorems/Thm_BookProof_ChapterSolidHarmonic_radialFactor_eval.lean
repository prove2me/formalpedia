-- Prove2me | Theorems.Thm_BookProof_ChapterSolidHarmonic_radialFactor_eval
-- name    : BookProof.ChapterSolidHarmonic.radialFactor_eval
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T14:54:37.328017+00:00
-- url     : https://prove2.me/theorems/a2fcc43a-5a54-4eeb-98f6-16732dc63d37
-- title:
--   `BookProof.ChapterSolidHarmonic.radialFactor_eval` (e : E) {l μ : ℕ} (hμ : μ ≤ l) {x : E} (hx : x ≠ 0) : radialFactor e l μ x = ‖x‖ ^ (l - μ) * (derivative^[μ] (legendre l)).eval (
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSolidHarmonic`.
--
--   `BookProof.ChapterSolidHarmonic.radialFactor_eval` (e : E) {l μ : ℕ} (hμ : μ ≤ l) {x : E} (hx : x ≠ 0) : radialFactor e l μ x = ‖x‖ ^ (l - μ) * (derivative^[μ] (legendre l)).eval (⟪e, x⟫_ℝ / ‖x‖)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSolidHarmonic.radialFactor_eval`.

-- Generated from ChapterSolidHarmonic.lean — theorem BookProof.ChapterSolidHarmonic.radialFactor_eval
import Definitions.Def_ChapterRadialLaplacian
import Definitions.Def_ChapterLaplacianProduct
import Definitions.Def_ChapterSolidHarmonicTools
import Mathlib
import Definitions.Def_ChapterSolidHarmonic
import Definitions.Def_ChapterLegendrePolynomial
open BookProof.ChapterLegendrePolynomial
open BookProof.ChapterSolidHarmonic



open Laplacian InnerProductSpace Polynomial
open BookProof.ChapterRadialLaplacian BookProof.ChapterLaplacianProduct
open BookProof.ChapterSolidHarmonicTools BookProof.ChapterLegendrePolynomial
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem BookProof.ChapterSolidHarmonic.radialFactor_eval (e : E) {l μ : ℕ} (hμ : μ ≤ l) {x : E} (hx : x ≠ 0) :
    radialFactor e l μ x
      = ‖x‖ ^ (l - μ) * (derivative^[μ] (legendre l)).eval (⟪e, x⟫_ℝ / ‖x‖) := by sorry
