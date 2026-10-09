-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_exists_finiteModes_graph_approx
-- name    : BookProof.NavierStokesFlow.IkebeKato.exists_finiteModes_graph_approx
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T23:21:50.515529+00:00
-- url     : https://prove2.me/theorems/46034855-c49d-4def-9a0a-2e169e6cd21b
-- title:
--   The Lean 4 theorem `exists_finiteModes_graph_approx` in the `ChapterNavierStokesIkebeKato` chapter of the timepiece formalization
-- statement:
--   Formal statement of `BookProof.NavierStokesFlow.IkebeKato.exists_finiteModes_graph_approx` from the timepiece Lean 4 formalization.
-- source:
--   https://github.com/leonardopedro/timepiece

-- Generated from ChapterNavierStokesIkebeKato.lean — theorem BookProof.NavierStokesFlow.IkebeKato.exists_finiteModes_graph_approx
import Mathlib
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.IkebeKato


open scoped ENNReal



open LpNat BookProof.FarisLavine

variable {ι : Type*}

theorem BookProof.NavierStokesFlow.IkebeKato.exists_finiteModes_graph_approx (c : ι → ℝ) (x : maxDom c) (ε : ℝ) (hε : 0 < ε) :
    ∃ y : maxDom c, (y : L2I ι) ∈ lpFiniteModes ι ∧
      ‖(y : L2I ι) - (x : L2I ι)‖ < ε ∧ ‖diagMax c y - diagMax c x‖ < ε := by sorry
