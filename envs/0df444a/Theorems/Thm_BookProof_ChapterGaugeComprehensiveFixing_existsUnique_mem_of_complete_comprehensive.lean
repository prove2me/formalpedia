-- Prove2me | Theorems.Thm_BookProof_ChapterGaugeComprehensiveFixing_existsUnique_mem_of_complete_comprehensive
-- name    : BookProof.ChapterGaugeComprehensiveFixing.existsUnique_mem_of_complete_comprehensive
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T10:56:13.22282+00:00
-- url     : https://prove2.me/theorems/cf92c565-183c-4ed0-b1cb-40aac99b634f
-- title:
--   `BookProof.ChapterGaugeComprehensiveFixing.existsUnique_mem_of_complete_comprehensive` (hcomp : IsComprehensiveGaugeFixing G S) (hcompl : IsCompleteGaugeFixing' G S) (x : X) : ∃! s
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGaugeComprehensiveFixing`.
--
--   `BookProof.ChapterGaugeComprehensiveFixing.existsUnique_mem_of_complete_comprehensive` (hcomp : IsComprehensiveGaugeFixing G S) (hcompl : IsCompleteGaugeFixing' G S) (x : X) : ∃! s : X, s ∈ S ∧ ∃ g : G, g • s = x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGaugeComprehensiveFixing.existsUnique_mem_of_complete_comprehensive`.

-- Generated from ChapterGaugeComprehensiveFixing.lean — theorem BookProof.ChapterGaugeComprehensiveFixing.existsUnique_mem_of_complete_comprehensive
import Mathlib
import Definitions.Def_ChapterGaugeComprehensiveFixing
import Definitions.Def_ChapterGaugeIncompleteFixing
open BookProof.ChapterGaugeIncompleteFixing
open BookProof.ChapterGaugeComprehensiveFixing



open BookProof.ChapterGaugeIncompleteFixing

variable {X : Type*} (G : Type*) [Group G] [MulAction G X]
variable {X : Type*} {G : Type*} [Group G] [MulAction G X] {S : Set X}

theorem BookProof.ChapterGaugeComprehensiveFixing.existsUnique_mem_of_complete_comprehensive
    (hcomp : IsComprehensiveGaugeFixing G S) (hcompl : IsCompleteGaugeFixing' G S)
    (x : X) : ∃! s : X, s ∈ S ∧ ∃ g : G, g • s = x := by sorry
