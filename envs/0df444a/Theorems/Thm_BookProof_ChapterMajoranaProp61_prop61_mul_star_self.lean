-- Prove2me | Theorems.Thm_BookProof_ChapterMajoranaProp61_prop61_mul_star_self
-- name    : BookProof.ChapterMajoranaProp61.prop61_mul_star_self
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-08T06:05:57.459447+00:00
-- url     : https://prove2.me/theorems/f0cbaf67-1d9a-4699-88cf-89c95398c5df
-- title:
--   Proposition 61, `U' (U')† = 1`.
-- statement:
--   **Proposition 61, `U' (U')† = 1`.**
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.ChapterMajoranaProp61.prop61_mul_star_self` (module `BookProof.MajoranaProp61`), line-linked source: `ChapterMajoranaProp61.lean` lines 123–147.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterMajoranaProp61.lean#L123-L147

-- Generated from ChapterMajoranaProp61.lean — theorem BookProof.ChapterMajoranaProp61.prop61_mul_star_self
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

set_option maxHeartbeats 2000000 in
-- the proof below is a large finite computation; the default heartbeat budget
-- is not enough to elaborate it
omit [StarModule ℝ 𝒜] hNE hNA in

theorem BookProof.ChapterMajoranaProp61.prop61_mul_star_self :
    Uprime U H g E Ni * star (Uprime U H g E Ni) = 1 := by sorry
