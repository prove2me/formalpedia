-- Prove2me | Theorems.Thm_BookProof_ChapterGaugeComprehensiveFixing_physical_ext_iff_comprehensive
-- name    : BookProof.ChapterGaugeComprehensiveFixing.physical_ext_iff_comprehensive
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T10:56:53.759378+00:00
-- url     : https://prove2.me/theorems/59a0b774-cc2c-4982-bc73-10fcbf067848
-- title:
--   `BookProof.ChapterGaugeComprehensiveFixing.physical_ext_iff_comprehensive` : (∀ f f' : X → ℝ, IsPhysicalObservable G f → IsPhysicalObservable G f' → (∀ s ∈ S, f s = f' s) → f = f')
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGaugeComprehensiveFixing`.
--
--   `BookProof.ChapterGaugeComprehensiveFixing.physical_ext_iff_comprehensive` : (∀ f f' : X → ℝ, IsPhysicalObservable G f → IsPhysicalObservable G f' → (∀ s ∈ S, f s = f' s) → f = f') ↔ IsComprehensiveGaugeFixing G S
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGaugeComprehensiveFixing.physical_ext_iff_comprehensive`.

-- Generated from ChapterGaugeComprehensiveFixing.lean — theorem BookProof.ChapterGaugeComprehensiveFixing.physical_ext_iff_comprehensive
import Mathlib
import Definitions.Def_ChapterGaugeComprehensiveFixing
import Definitions.Def_ChapterGaugeIncompleteFixing
open BookProof.ChapterGaugeIncompleteFixing
open BookProof.ChapterGaugeComprehensiveFixing



open BookProof.ChapterGaugeIncompleteFixing


variable {X : Type*} {G : Type*} [Group G] [MulAction G X] {S : Set X}

theorem BookProof.ChapterGaugeComprehensiveFixing.physical_ext_iff_comprehensive :
    (∀ f f' : X → ℝ, IsPhysicalObservable G f → IsPhysicalObservable G f' →
        (∀ s ∈ S, f s = f' s) → f = f') ↔ IsComprehensiveGaugeFixing G S := by sorry
