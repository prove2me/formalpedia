-- Prove2me | Theorems.Thm_BookProof_ChapterSirkSpectralGeometry_crouzeix_domain_convexHull
-- name    : BookProof.ChapterSirkSpectralGeometry.crouzeix_domain_convexHull
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T04:32:21.263433+00:00
-- url     : https://prove2.me/theorems/827bf6da-08b8-41a5-864b-22653f71a815
-- title:
--   (V : G →L[ℂ] E) (X : E →L[ℂ] E) (hViso : ∀ x : G, ‖V x‖ = ‖x‖) (S : Set ℂ) (hconv : Convex ℝ S) (hS : numRange X ⊆ S) : convexHull ℝ (numRange (compress V X)) ⊆ S
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkSpectralGeometry.crouzeix_domain_convexHull` (module `BookProof.ChapterSirkSpectralGeometry`), source chapter `BookProof/ChapterChapterSirkSpectralGeometry.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkSpectralGeometry.lean

-- Generated from ChapterSirkSpectralGeometry.lean — theorem BookProof.ChapterSirkSpectralGeometry.crouzeix_domain_convexHull
import Mathlib
import Definitions.Def_ChapterSirkSpectralGeometry
open BookProof.ChapterSirkSpectralGeometry








noncomputable section


open BookProof.ChapterH4 BookProof.ChapterH6 BookProof.ChapterH9
open BookProof.ChapterSirkEndToEnd BookProof.HashimotoShiftInvert BookProof.FarisLavine






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {Dom : Submodule ℂ F}







variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

theorem BookProof.ChapterSirkSpectralGeometry.crouzeix_domain_convexHull (V : G →L[ℂ] E) (X : E →L[ℂ] E)
    (hViso : ∀ x : G, ‖V x‖ = ‖x‖) (S : Set ℂ) (hconv : Convex ℝ S) (hS : numRange X ⊆ S) :
    convexHull ℝ (numRange (compress V X)) ⊆ S := by sorry
