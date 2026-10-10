-- Prove2me | Theorems.Thm_BookProof_ChapterA3_mgammaLin_orthogonal_invariant
-- name    : BookProof.ChapterA3.mgammaLin_orthogonal_invariant
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T09:27:26.24498+00:00
-- url     : https://prove2.me/theorems/c7f40326-bf82-4b27-b34d-014053384522
-- title:
--   `BookProof.ChapterA3.mgammaLin_orthogonal_invariant` {W : Submodule ℂ MajoranaSpace} (hW : ∀ μ, ∀ x ∈ W, mgammaLin μ x ∈ W) (μ : Fin 4) {y : MajoranaSpace} (hy : y ∈ Wᗮ) : mgammaLi
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPauliCommutant`.
--
--   `BookProof.ChapterA3.mgammaLin_orthogonal_invariant` {W : Submodule ℂ MajoranaSpace} (hW : ∀ μ, ∀ x ∈ W, mgammaLin μ x ∈ W) (μ : Fin 4) {y : MajoranaSpace} (hy : y ∈ Wᗮ) : mgammaLin μ y ∈ Wᗮ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.mgammaLin_orthogonal_invariant`.

-- Generated from ChapterPauliCommutant.lean — theorem BookProof.ChapterA3.mgammaLin_orthogonal_invariant
import Mathlib
import Definitions.Def_ChapterPauliCommutant
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix

theorem BookProof.ChapterA3.mgammaLin_orthogonal_invariant {W : Submodule ℂ MajoranaSpace}
    (hW : ∀ μ, ∀ x ∈ W, mgammaLin μ x ∈ W) (μ : Fin 4) {y : MajoranaSpace} (hy : y ∈ Wᗮ) :
    mgammaLin μ y ∈ Wᗮ := by sorry
