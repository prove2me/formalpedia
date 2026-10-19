-- Prove2me | Theorems.Thm_BookProof_ChapterCyclicDirectSum_starProjection_eq_of_hasSum
-- name    : BookProof.ChapterCyclicDirectSum.starProjection_eq_of_hasSum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T02:09:42.904473+00:00
-- url     : https://prove2.me/theorems/7fdc83a9-a168-4b4f-9ca6-1255556f03b3
-- title:
--   `BookProof.ChapterCyclicDirectSum.starProjection_eq_of_hasSum` {ι : Type*} {V : ι → Submodule ℂ H} [∀ i, (V i).HasOrthogonalProjection] (hV : OrthogonalFamily ℂ (fun i => (V i)) fu
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCyclicDirectSum`.
--
--   `BookProof.ChapterCyclicDirectSum.starProjection_eq_of_hasSum` {ι : Type*} {V : ι → Submodule ℂ H} [∀ i, (V i).HasOrthogonalProjection] (hV : OrthogonalFamily ℂ (fun i => (V i)) fun i => (V i).subtypeₗᵢ) {c : ι → H} (hc : ∀ i, c i ∈ V i) {v : H} (h : HasSum c v) (j : ι) : (V j).starProjection v = c j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCyclicDirectSum.starProjection_eq_of_hasSum`.

-- Generated from ChapterCyclicDirectSum.lean — theorem BookProof.ChapterCyclicDirectSum.starProjection_eq_of_hasSum
import Definitions.Def_ChapterCyclicDecomposition
import Mathlib
import Definitions.Def_ChapterCyclicDirectSum
open BookProof.ChapterCyclicDirectSum


noncomputable section

open MeasureTheory Complex


open BookProof.ChapterCyclicDecomposition

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : H →L[ℂ] H) (hT : IsStarNormal T)

theorem BookProof.ChapterCyclicDirectSum.starProjection_eq_of_hasSum {ι : Type*} {V : ι → Submodule ℂ H}
    [∀ i, (V i).HasOrthogonalProjection]
    (hV : OrthogonalFamily ℂ (fun i => (V i)) fun i => (V i).subtypeₗᵢ)
    {c : ι → H} (hc : ∀ i, c i ∈ V i) {v : H} (h : HasSum c v) (j : ι) :
    (V j).starProjection v = c j := by sorry
