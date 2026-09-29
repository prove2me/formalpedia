-- Prove2me | Theorems.Thm_BookProof_ChapterMajoranaProp61_prop61_isUnit
-- name    : BookProof.ChapterMajoranaProp61.prop61_isUnit
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-08T02:00:34.343896+00:00
-- url     : https://prove2.me/theorems/b6a6cd2e-0e57-458d-8e91-0ac1bfddaf30
-- title:
--   Proposition 61 (headline).** The boost intertwiner `U'` is unitary: it has the two-sided inverse `(U')†`
-- statement:
--   **Proposition 61 (headline).**  The boost intertwiner `U'` is unitary: it has the
--   two-sided inverse `(U')†`.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.ChapterMajoranaProp61.prop61_isUnit` (module `BookProof.MajoranaProp61`), line-linked source: `ChapterMajoranaProp61.lean` lines 149–158.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterMajoranaProp61.lean#L149-L158

-- Generated from ChapterMajoranaProp61.lean — theorem BookProof.ChapterMajoranaProp61.prop61_isUnit
import Mathlib
import Definitions.Def_ChapterMajoranaProp61
open BookProof.ChapterMajoranaProp61













variable {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Algebra ℝ 𝒜] [StarModule ℝ 𝒜]




variable (U H g E N Ni : 𝒜) (m : ℝ)
  (hU₁ : star U * U = 1) (hU₂ : U * star U = 1)
  (hg_sa : star g = g) (hg2 : g * g = 1)
  (hH_sa : star H = H)
  (hanti : H * g + g * H = (2 * m) • (1 : 𝒜))
  (hE_sa : star E = E)
  (hE2 : E * E = U * (H * H) * star U)
  (hEA : E * Aop U H g = Aop U H g * E)
  (hN_sa : star N = N)
  (hN2 : N * N = (2 : ℝ) • (E * E) + (2 * m) • E)
  (hNi₁ : N * Ni = 1) (hNi₂ : Ni * N = 1)
  (hNE : N * E = E * N)
  (hNA : N * Aop U H g = Aop U H g * N)

include hU₁ hU₂ hg_sa hg2 hH_sa hanti hE_sa hE2 hEA hN_sa hN2 hNi₁ hNi₂ hNE hNA

theorem BookProof.ChapterMajoranaProp61.prop61_isUnit : IsUnit (Uprime U H g E Ni) := by sorry
