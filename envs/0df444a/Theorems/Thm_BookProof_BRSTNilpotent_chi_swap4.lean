-- Prove2me | Theorems.Thm_BookProof_BRSTNilpotent_chi_swap4
-- name    : BookProof.BRSTNilpotent.chi_swap4
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T14:21:26.747108+00:00
-- url     : https://prove2.me/theorems/e5270d58-441d-43c5-a265-24581a79730d
-- title:
--   Four creation operators can be reordered in pairs with sign $+1$
-- statement:
--   Four creation operators can be reordered in pairs with sign $+1$.
--
--   For ghost creation operators satisfying the canonical anticommutation relations,
--   $$
--   \chi_a\chi_b\chi_c\chi_d = \chi_c\chi_d\chi_a\chi_b.
--   $$
--
--   Moving one anticommuting pair past another is an even permutation of the four fermionic operators, so no sign is introduced.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.BRSTNilpotent.chi_swap4` (module `BookProof.BRSTNilpotent`), line-linked source: `ChapterBRSTNilpotent.lean` lines 84–102.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterBRSTNilpotent.lean#L84-L102

-- Generated from ChapterBRSTNilpotent.lean — theorem BookProof.BRSTNilpotent.chi_swap4
import Mathlib
import Definitions.Def_ChapterBRSTNilpotent
open BookProof.BRSTNilpotent












variable {R : Type*} [Ring R] [Algebra ℝ R]
variable {n : ℕ}

theorem BookProof.BRSTNilpotent.chi_swap4 (χ β : Fin n → R) (hCAR : GhostCAR χ β) (a b c d : Fin n) :
    χ a * χ b * χ c * χ d = χ c * χ d * χ a * χ b := by sorry
