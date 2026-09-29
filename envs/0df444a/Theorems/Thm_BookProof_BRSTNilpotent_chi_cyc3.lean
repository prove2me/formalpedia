-- Prove2me | Theorems.Thm_BookProof_BRSTNilpotent_chi_cyc3
-- name    : BookProof.BRSTNilpotent.chi_cyc3
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T14:20:36.29872+00:00
-- url     : https://prove2.me/theorems/c6b05ed8-f544-4aba-9109-068cf6a7e9e9
-- title:
--   Cyclic rotation of three creation operators has sign $+1$
-- statement:
--   Cyclic rotation of three creation operators has sign $+1$.
--
--   For ghost creation operators with canonical anticommutation relations,
--   $$
--   \chi_a\chi_b\chi_c = \chi_b\chi_c\chi_a.
--   $$
--
--   A cyclic permutation of three anticommuting elements is an even permutation.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.BRSTNilpotent.chi_cyc3` (module `BookProof.BRSTNilpotent`), line-linked source: `ChapterBRSTNilpotent.lean` lines 104–116.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterBRSTNilpotent.lean#L104-L116

-- Generated from ChapterBRSTNilpotent.lean — theorem BookProof.BRSTNilpotent.chi_cyc3
import Mathlib
import Definitions.Def_ChapterBRSTNilpotent
open BookProof.BRSTNilpotent












variable {R : Type*} [Ring R] [Algebra ℝ R]
variable {n : ℕ}

theorem BookProof.BRSTNilpotent.chi_cyc3 (χ β : Fin n → R) (hCAR : GhostCAR χ β) (a b c : Fin n) :
    χ a * χ b * χ c = χ b * χ c * χ a := by sorry
