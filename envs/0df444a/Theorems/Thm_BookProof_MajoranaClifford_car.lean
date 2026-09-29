-- Prove2me | Theorems.Thm_BookProof_MajoranaClifford_car
-- name    : BookProof.MajoranaClifford.car
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-08T02:07:35.231381+00:00
-- url     : https://prove2.me/theorems/6861db93-4d5b-46db-9e8d-8a8cc0a8bace
-- title:
--   The canonical anticommutation relation (CAR)** `{a(v), a(w)} = a(v)·a(w) + a(w)·a(v) = 2⟪v,w⟫·1`, the polarization of the Clifford relation
-- statement:
--   **The canonical anticommutation relation (CAR)**
--   `{a(v), a(w)} = a(v)·a(w) + a(w)·a(v) = 2⟪v,w⟫·1`, the polarization of the
--   Clifford relation.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.MajoranaClifford.car` (module `BookProof.MajoranaClifford`), line-linked source: `ChapterMajoranaClifford.lean` lines 103–109.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterMajoranaClifford.lean#L103-L109

-- Generated from ChapterMajoranaClifford.lean — theorem BookProof.MajoranaClifford.car
import Mathlib
import Definitions.Def_ChapterMajoranaClifford
open BookProof.MajoranaClifford









open RealInnerProductSpace CliffordAlgebra QuadraticMap


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem BookProof.MajoranaClifford.car (v w : V) :
    a v * a w + a w * a v
      = algebraMap ℝ (CliffordAlgebra (Qform (V := V))) (2 * ⟪v, w⟫) := by sorry
