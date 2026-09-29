-- Prove2me | Theorems.Thm_BookProof_BRSTNilpotent_quartic_term_zero
-- name    : BookProof.BRSTNilpotent.quartic_term_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T14:55:33.517718+00:00
-- url     : https://prove2.me/theorems/0f975d74-2c87-4f5c-a92a-77126340efdf
-- title:
--   The purely quartic ghost term vanishes
-- statement:
--   The purely quartic ghost term vanishes.
--
--   Let $f_{abe}$ be structure constants, $\chi$ the ghost creation operators and $\beta$ the ghost annihilation operators satisfying canonical anticommutation relations. The fully normal-ordered piece of $Q^2$,
--   $$
--   \sum_{a,b,e,d,g,h} f_{abe}\,f_{dgh}\,(\chi_a\chi_b\chi_d\chi_g\,\beta_e\beta_h)=0,
--   $$
--
--   vanishes: it is antisymmetric under exchanging the two $Q$-factors (even sign on the four $\chi$'s, odd sign on the two $\beta$'s), hence equals its own negative.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.BRSTNilpotent.quartic_term_zero` (module `BookProof.BRSTNilpotent`), line-linked source: `ChapterBRSTNilpotent.lean` lines 124–153.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterBRSTNilpotent.lean#L124-L153

-- Generated from ChapterBRSTNilpotent.lean — theorem BookProof.BRSTNilpotent.quartic_term_zero
import Mathlib
import Definitions.Def_ChapterBRSTNilpotent
open BookProof.BRSTNilpotent












variable {R : Type*} [Ring R] [Algebra ℝ R]
variable {n : ℕ}

theorem BookProof.BRSTNilpotent.quartic_term_zero (f : Fin n → Fin n → Fin n → ℝ) (χ β : Fin n → R)
    (hCAR : GhostCAR χ β) :
    (∑ a, ∑ b, ∑ e, ∑ d, ∑ g, ∑ h,
      (f a b e * f d g h) • (χ a * χ b * χ d * χ g * β e * β h)) = 0 := by sorry
