-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gb80_uniform_refinement_index_bounds
-- name    : AvramDividend.Classical.avram_gb80_uniform_refinement_index_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T13:44:37.322201+00:00
-- url     : https://prove2.me/theorems/df94f1f7-7d3b-4dc6-8c12-f5c81988c831
-- title:
--   Common-refinement quotient indices stay inside coarse cells
-- statement:
--   For two unrelated uniform-grid resolutions m+1 and p+1, every common refinement index r below their product belongs to coarse interval index floor(r/(p+1)), which is at most m, and lies between the left and right integer boundaries of that coarse cell. This deterministic arithmetic atom supports the exact original Gaussian two-grid reindexing needed for gbB60 and gbB64.

import Mathlib

theorem AvramDividend.Classical.avram_gb80_uniform_refinement_index_bounds
    (m p r : ℕ) (hr : r < (m + 1) * (p + 1)) :
    r / (p + 1) ≤ m ∧
    (r / (p + 1)) * (p + 1) ≤ r ∧
    r < (r / (p + 1) + 1) * (p + 1) := by sorry
