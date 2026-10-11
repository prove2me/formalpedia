-- Prove2me | Theorems.Thm_BookProof_ChapterSolidHarmonic_solidHarmonic_euler
-- name    : BookProof.ChapterSolidHarmonic.solidHarmonic_euler
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T14:54:23.488161+00:00
-- url     : https://prove2.me/theorems/d3c7a4d9-29c4-41ea-87d2-4a3ea0ad007a
-- title:
--   `BookProof.ChapterSolidHarmonic.solidHarmonic_euler` (u v e : E) {l μ : ℕ} (hμ : μ ≤ l) (x : E) : fderiv ℝ (solidHarmonic u v e l μ) x x = (l : ℝ) * solidHarmonic u v e l μ x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSolidHarmonic`.
--
--   `BookProof.ChapterSolidHarmonic.solidHarmonic_euler` (u v e : E) {l μ : ℕ} (hμ : μ ≤ l) (x : E) : fderiv ℝ (solidHarmonic u v e l μ) x x = (l : ℝ) * solidHarmonic u v e l μ x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSolidHarmonic.solidHarmonic_euler`.

-- Generated from ChapterSolidHarmonic.lean — theorem BookProof.ChapterSolidHarmonic.solidHarmonic_euler
import Definitions.Def_ChapterRadialLaplacian
import Definitions.Def_ChapterLaplacianProduct
import Definitions.Def_ChapterSolidHarmonicTools
import Definitions.Def_ChapterLegendrePolynomial
import Mathlib
import Definitions.Def_ChapterSolidHarmonic
open BookProof.ChapterSolidHarmonic



open Laplacian InnerProductSpace Polynomial
open BookProof.ChapterRadialLaplacian BookProof.ChapterLaplacianProduct
open BookProof.ChapterSolidHarmonicTools BookProof.ChapterLegendrePolynomial
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem BookProof.ChapterSolidHarmonic.solidHarmonic_euler (u v e : E) {l μ : ℕ} (hμ : μ ≤ l) (x : E) :
    fderiv ℝ (solidHarmonic u v e l μ) x x = (l : ℝ) * solidHarmonic u v e l μ x := by sorry
