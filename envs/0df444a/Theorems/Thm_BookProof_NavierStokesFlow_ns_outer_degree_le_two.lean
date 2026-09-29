-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_ns_outer_degree_le_two
-- name    : BookProof.NavierStokesFlow.ns_outer_degree_le_two
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T11:53:58.655382+00:00
-- url     : https://prove2.me/theorems/db465e40-ed45-4eb6-b2f0-c13a32747742
-- title:
--   The Lean 4 theorem `ns_outer_degree_le_two` in the `ChapterNavierStokesFlow` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `ns_outer_degree_le_two` in the `ChapterNavierStokesFlow` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFlow.lean — theorem BookProof.NavierStokesFlow.ns_outer_degree_le_two
import Mathlib
import Definitions.Def_ChapterNavierStokesFlow
open BookProof.NavierStokesFlow


open scoped BigOperators Matrix Kronecker ComplexOrder TensorProduct

variable {n : ℕ}

theorem BookProof.NavierStokesFlow.ns_outer_degree_le_two {m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (h : Matrix (Fin m) (Fin m) ℂ) :
    nsSecondQuant A h
        = ∑ a : Fin m × Fin m,
            h a.1 a.2 • (([Sum.inl a.1, Sum.inr a.2].map (nsOuterGen A)).prod)
      ∧ ∀ a : Fin m × Fin m, ([Sum.inl a.1, Sum.inr a.2] : List (Fin m ⊕ Fin m)).length ≤ 2 := by sorry
