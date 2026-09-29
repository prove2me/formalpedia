-- Prove2me | Theorems.Thm_BookProof_BRSTNilpotent_beta_move
-- name    : BookProof.BRSTNilpotent.beta_move
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T14:14:33.795453+00:00
-- url     : https://prove2.me/theorems/d995c818-0f9e-4558-aadf-d426341878cd
-- title:
--   Normal ordering of a single annihilation operator
-- statement:
--   Normal ordering of a single annihilation operator.
--
--   Let $\chi_a,\beta_a$ be ghost creation and annihilation operators satisfying the canonical anticommutation relations in a ring $R$ over $\mathbb R$. Pushing the annihilation operator $\beta_e$ past a pair of creation operators $\chi_d \chi_g$ produces two contraction terms plus a normal-ordered remainder:
--   $$
--   \beta_e\,(\chi_d\chi_g) = (e=d\;?\;\chi_g : 0) - (e=g\;?\;\chi_d : 0) + \chi_d\chi_g\,\beta_e.
--   $$
--
--   This is the fundamental rearrangement used to normal-order powers of the BRST charge and is applied throughout the nilpotency proof.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.BRSTNilpotent.beta_move` (module `BookProof.BRSTNilpotent`), line-linked source: `ChapterBRSTNilpotent.lean` lines 63–82.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterBRSTNilpotent.lean#L63-L82

-- Generated from ChapterBRSTNilpotent.lean — theorem BookProof.BRSTNilpotent.beta_move
import Mathlib
import Definitions.Def_ChapterBRSTNilpotent
open BookProof.BRSTNilpotent












variable {R : Type*} [Ring R] [Algebra ℝ R]
variable {n : ℕ}

theorem BookProof.BRSTNilpotent.beta_move (χ β : Fin n → R) (hCAR : GhostCAR χ β) (e d g : Fin n) :
    β e * (χ d * χ g)
      = (if e = d then χ g else 0) - (if e = g then χ d else 0) + χ d * χ g * β e := by sorry
