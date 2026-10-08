-- Prove2me | Theorems.Thm_BookProof_FreeEMField_emFieldStrength_gauge_invariant
-- name    : BookProof.FreeEMField.emFieldStrength_gauge_invariant
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T10:24:53.488412+00:00
-- url     : https://prove2.me/theorems/551bd4a6-bd53-4c16-9639-2b7bb0366fbd
-- title:
--   `BookProof.FreeEMField.emFieldStrength_gauge_invariant` (δ : Fin 3 → R → R) (A : Fin 3 → R) (θ : R) (hadd : ∀ j x y, δ j (x + y) = δ j x + δ j y) (hcomm : ∀ j k x, δ j (δ k x) = δ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeEMField`.
--
--   `BookProof.FreeEMField.emFieldStrength_gauge_invariant` (δ : Fin 3 → R → R) (A : Fin 3 → R) (θ : R) (hadd : ∀ j x y, δ j (x + y) = δ j x + δ j y) (hcomm : ∀ j k x, δ j (δ k x) = δ k (δ j x)) (j k : Fin 3) : emFieldStrength δ (fun i => A i + δ i θ) j k = emFieldStrength δ A j k
--
--   Formalization note: Lean 4 identifier `BookProof.FreeEMField.emFieldStrength_gauge_invariant`.

-- Generated from ChapterFreeEMField.lean — theorem BookProof.FreeEMField.emFieldStrength_gauge_invariant
import Definitions.Def_ChapterYangMillsFieldStrength
import Mathlib
import Definitions.Def_ChapterFreeEMField
open BookProof.FreeEMField



open BookProof.YangMillsFieldStrength


variable {R : Type*} [Ring R]

theorem BookProof.FreeEMField.emFieldStrength_gauge_invariant
    (δ : Fin 3 → R → R) (A : Fin 3 → R) (θ : R)
    (hadd : ∀ j x y, δ j (x + y) = δ j x + δ j y)
    (hcomm : ∀ j k x, δ j (δ k x) = δ k (δ j x))
    (j k : Fin 3) :
    emFieldStrength δ (fun i => A i + δ i θ) j k = emFieldStrength δ A j k := by sorry
