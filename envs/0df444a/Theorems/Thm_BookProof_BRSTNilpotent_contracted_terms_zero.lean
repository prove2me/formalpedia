-- Prove2me | Theorems.Thm_BookProof_BRSTNilpotent_contracted_terms_zero
-- name    : BookProof.BRSTNilpotent.contracted_terms_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T14:54:53.565718+00:00
-- url     : https://prove2.me/theorems/185ed7c6-1ec7-464d-93dc-a4c3bc18c544
-- title:
--   The contracted (two-contraction) terms of $Q^2$ vanish by the Jacobi identity
-- statement:
--   The contracted (two-contraction) terms of $Q^2$ vanish by the Jacobi identity.
--
--   Let $f_{abe}$ be structure constants satisfying the Jacobi identity and $\chi,\beta$ canonical anticommuting ghost operators. The sum of the terms in $Q^2$ that arise from contracting two pairs of ghosts,
--   $$
--   \sum_{a,b,c,e,d} f_{abe}\,f_{cd}\,(\cdots)=0,
--   $$
--
--   vanishes precisely because $f$ satisfies the Jacobi identity. Together with `quartic_term_zero` this leaves only the cubic (one-contraction) remainder, which is handled separately in the nilpotency proof.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.BRSTNilpotent.contracted_terms_zero` (module `BookProof.BRSTNilpotent`), line-linked source: `ChapterBRSTNilpotent.lean` lines 162–197.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterBRSTNilpotent.lean#L162-L197

-- Generated from ChapterBRSTNilpotent.lean — theorem BookProof.BRSTNilpotent.contracted_terms_zero
import Mathlib
import Definitions.Def_ChapterBRSTNilpotent
open BookProof.BRSTNilpotent












variable {R : Type*} [Ring R] [Algebra ℝ R]
variable {n : ℕ}

theorem BookProof.BRSTNilpotent.contracted_terms_zero (f : Fin n → Fin n → Fin n → ℝ) (χ β : Fin n → R)
    (hCAR : GhostCAR χ β)
    (hjac : ∀ a b c h : Fin n,
      ∑ e, (f a b e * f e c h + f b c e * f e a h + f c a e * f e b h) = 0) :
    (∑ a, ∑ b, ∑ e, ∑ g, ∑ h,
      (f a b e * f e g h) • (χ a * χ b * χ g * β h)) = 0 := by sorry
