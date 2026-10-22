-- Prove2me | Theorems.Thm_BookProof_ChapterMajoranaProp61_prop61_isUnit_inc
-- name    : BookProof.ChapterMajoranaProp61.prop61_isUnit_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T14:26:32.72845+00:00
-- url     : https://prove2.me/theorems/bdb0f799-1638-46fe-a004-d572de959281
-- title:
--   Proposition 61 (headline).** The boost intertwiner `U'` is unitary: it has the two-sided inverse `(U')†`
-- statement:
--   **Proposition 61 (headline).**  The boost intertwiner `U'` is unitary: it has the
--   two-sided inverse `(U')†`.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.ChapterMajoranaProp61.prop61_isUnit_inc` (module `BookProof.MajoranaProp61`), line-linked source: `ChapterMajoranaProp61.lean` lines 149–158.
--
--   Replaces the retired node `BookProof.ChapterMajoranaProp61.prop61_isUnit`, whose stored statement omitted the `hE2`, `hEA`, `hE_sa`, `hH_sa`, `hN2`, `hNA`, `hNE`, `hN_sa`, `hNi₁`, `hNi₂`, `hU₁`, `hU₂`, `hanti`, `hg2`, `hg_sa` hypothesis binder (dropped `include`).
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterMajoranaProp61.lean#L149-L158

-- Generated from ChapterMajoranaProp61.lean — theorem BookProof.ChapterMajoranaProp61.prop61_isUnit_inc
import Mathlib
import Definitions.Def_ChapterMajoranaProp61
import Definitions.Def_ChapterMajoranaFourier
open BookProof.ChapterMajoranaFourier
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

include hE2 hEA hE_sa hH_sa hN2 hNA hNE hN_sa hNi₁ hNi₂ hU₁ hU₂ hanti hg2 hg_sa in

theorem BookProof.ChapterMajoranaProp61.prop61_isUnit_inc : IsUnit (Uprime U H g E Ni) := by sorry
