-- Prove2me | Theorems.Thm_BookProof_FarisLavine_exists_weak_graph_limit
-- name    : BookProof.FarisLavine.exists_weak_graph_limit
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:23:09.229394+00:00
-- url     : https://prove2.me/theorems/c849569e-137d-4682-92fd-61ba9fac17e9
-- title:
--   The Lean 4 theorem `exists_weak_graph_limit` in the `ChapterFarisLavineCore` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `exists_weak_graph_limit` in the `ChapterFarisLavineCore` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFarisLavineCore.lean

-- Generated from ChapterFarisLavineCore.lean — theorem BookProof.FarisLavine.exists_weak_graph_limit
import Mathlib
import Definitions.Def_ChapterFarisLavineCore
open BookProof.FarisLavine












variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

theorem BookProof.FarisLavine.exists_weak_graph_limit [CompleteSpace F] (H : D →ₗ[ℂ] F) (hH : SymmetricOn D H)
    (d : ℝ) (hd : d ≠ 0)
    (hdense : Dense (Set.range fun x : D => H x - ((d : ℂ) * Complex.I) • (x : F)))
    (y : F) :
    ∃ u z : F, (∀ v : D, (inner ℂ (H v) u : ℂ) = inner ℂ (v : F) z) ∧
      z - ((d : ℂ) * Complex.I) • u = y ∧ (inner ℂ z u : ℂ).im = 0 := by sorry
