-- Prove2me | Theorems.Thm_BookProof_CarlemanSimplex_flux_identityQ
-- name    : BookProof.CarlemanSimplex.flux_identityQ
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-07T22:48:31.636313+00:00
-- url     : https://prove2.me/theorems/0f03e6ac-ee50-4f37-a1de-5a1677302bbf
-- title:
--   `BookProof.CarlemanSimplex.flux_identityQ` (hM : ∀ i j, M j i = (starRingEnd ℂ) (M i j)) (hrec : LadderRecQ u lam w W M z) (N : ℕ) : z.im * (∑ a ∈ simplexF d N, ‖u a‖ ^ 2) = (∑ i,
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanSimplex`.
--
--   `BookProof.CarlemanSimplex.flux_identityQ` (hM : ∀ i j, M j i = (starRingEnd ℂ) (M i j)) (hrec : LadderRecQ u lam w W M z) (N : ℕ) : z.im * (∑ a ∈ simplexF d N, ‖u a‖ ^ 2) = (∑ i, (∑ a ∈ sBd d N 1, rtermP u (w i) (fun b => rc1 b i) (Finsupp.single i 1) a).im) + ∑ i, ∑ j, (∑ a ∈ sBd d N 2, rtermP u (W i j) (fun b => rcp b i j) (pvec i j) a).im
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanSimplex.flux_identityQ`.

-- Generated from ChapterCarlemanSimplex.lean — theorem BookProof.CarlemanSimplex.flux_identityQ
import Definitions.Def_ChapterHermiteCarlemanEsaPromoted
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Mathlib
import Definitions.Def_ChapterCarlemanSimplexPromoted
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.CarlemanSimplex



open Finset
open BookProof.HermiteCarleman BookProof.CarlemanTwoStep

noncomputable section

variable {d : ℕ}

variable {u : (Fin d →₀ ℕ) → ℂ}
variable {lam : (Fin d →₀ ℕ) → ℝ} {w : Fin d → ℂ} {W M : Fin d → Fin d → ℂ} {z : ℂ}

theorem BookProof.CarlemanSimplex.flux_identityQ (hM : ∀ i j, M j i = (starRingEnd ℂ) (M i j))
    (hrec : LadderRecQ u lam w W M z) (N : ℕ) :
    z.im * (∑ a ∈ simplexF d N, ‖u a‖ ^ 2)
      = (∑ i, (∑ a ∈ sBd d N 1, rtermP u (w i) (fun b => rc1 b i) (Finsupp.single i 1) a).im)
        + ∑ i, ∑ j,
            (∑ a ∈ sBd d N 2, rtermP u (W i j) (fun b => rcp b i j) (pvec i j) a).im := by sorry
