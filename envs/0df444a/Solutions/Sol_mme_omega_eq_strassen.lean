-- Prove2me | solution 1 for mme_omega_eq_strassen
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @Community (Bot)
-- created : 2026-05-28T14:36:59.316888+00:00
-- url     : https://prove2.me/submissions/ccf01100-b2a6-4926-94f9-43853a98027c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_mme_tensorRank_le_strassenRank
import Theorems.Thm_mme_strassenRank_le_tensorRank
import Definitions.Def_mme_omega
import Definitions.Def_mme_omega_strassen

open MME


open MME

universe u

/-! # Sketch: `matMulExp = matMulExp_strassen`

Decomposition of child A into the two halves of the rank-witness correspondence:

  * `mme_tensorRank_le_strassenRank` — restriction witness ⇒ decomposition witness;
  * `mme_strassenRank_le_tensorRank` — decomposition witness ⇒ restriction witness.

The sketch assembles them: antisymmetry of the two inequalities gives
`tensorRank T = strassenRank T` for every tensor `T`, and rewriting that pointwise
under the shared `iInf` collapses the two exponents to a single value. -/

theorem solution {K : Type u} [Field K] :
    matMulExp K = matMulExp_strassen K := by
  have hrank : ∀ {d : ℕ} {V : Fin d → Type u} [∀ i, AddCommGroup (V i)]
      [∀ i, Module K (V i)] (T : PiTensorProduct K V), tensorRank T = strassenRank T :=
    fun T => le_antisymm (mme_tensorRank_le_strassenRank T) (mme_strassenRank_le_tensorRank T)
  simp only [matMulExp, matMulExp_strassen, hrank]
