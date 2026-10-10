-- Prove2me | Theorems.Thm_BookProof_ChapterLittleGroup_prop79
-- name    : BookProof.ChapterLittleGroup.prop79
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:31:19.697861+00:00
-- url     : https://prove2.me/theorems/c1056ec5-50b6-47ab-97dd-40c86206cdc5
-- title:
--   `BookProof.ChapterLittleGroup.prop79` (q : K → G) (hq : Function.Injective q) (l₀ : K) (α : K → G) (Λ : G → K → K) (hα : ∀ k, α k * q l₀ * (α k)⁻¹ = q k) (hΛ : ∀ (S : G)...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLittleGroup`.
--
--   `BookProof.ChapterLittleGroup.prop79` (q : K → G) (hq : Function.Injective q) (l₀ : K) (α : K → G) (Λ : G → K → K) (hα : ∀ k, α k * q l₀ * (α k)⁻¹ = q k) (hΛ : ∀ (S : G) (k : K), S * q k * S⁻¹ = q (Λ S k)) (k : K) : Hset α Λ k = (littleGroup q l₀ : Set G)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLittleGroup.prop79`.

-- Generated from ChapterLittleGroup.lean — theorem BookProof.ChapterLittleGroup.prop79
import Mathlib
import Definitions.Def_ChapterLittleGroup
open BookProof.ChapterLittleGroup



variable {G : Type*} [Group G] {K : Type*}

theorem BookProof.ChapterLittleGroup.prop79 (q : K → G) (hq : Function.Injective q) (l₀ : K)
    (α : K → G) (Λ : G → K → K)
    (hα : ∀ k, α k * q l₀ * (α k)⁻¹ = q k)
    (hΛ : ∀ (S : G) (k : K), S * q k * S⁻¹ = q (Λ S k))
    (k : K) :
    Hset α Λ k = (littleGroup q l₀ : Set G) := by sorry
