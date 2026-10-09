-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentFidelity_bornWeightC_eq_fidelity_normalized
-- name    : BookProof.ChapterCoherentFidelity.bornWeightC_eq_fidelity_normalized
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:51:41.168209+00:00
-- url     : https://prove2.me/theorems/5bdb3f5e-60b6-4bae-a3e8-391124ab798a
-- title:
--   `BookProof.ChapterCoherentFidelity.bornWeightC_eq_fidelity_normalized` (q : EuclideanSpace ℂ (Fin n)) (k : Fin m → EuclideanSpace ℂ (Fin n)) (j : Fin m) : bornWeightC q k j = fidel
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentFidelity`.
--
--   `BookProof.ChapterCoherentFidelity.bornWeightC_eq_fidelity_normalized` (q : EuclideanSpace ℂ (Fin n)) (k : Fin m → EuclideanSpace ℂ (Fin n)) (j : Fin m) : bornWeightC q k j = fidelityC q (k j) / ∑ l, fidelityC q (k l)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentFidelity.bornWeightC_eq_fidelity_normalized`.

-- Generated from ChapterCoherentFidelity.lean — theorem BookProof.ChapterCoherentFidelity.bornWeightC_eq_fidelity_normalized
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib
import Definitions.Def_ChapterCoherentFidelity
import Definitions.Def_ChapterCoherentOverlapComplex
open BookProof.ChapterCoherentOverlapComplex
open BookProof.ChapterCoherentFidelity


open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlapComplex BookProof.ChapterSoftmaxSharpness

variable {n m : ℕ}

theorem BookProof.ChapterCoherentFidelity.bornWeightC_eq_fidelity_normalized (q : EuclideanSpace ℂ (Fin n))
    (k : Fin m → EuclideanSpace ℂ (Fin n)) (j : Fin m) :
    bornWeightC q k j = fidelityC q (k j) / ∑ l, fidelityC q (k l) := by sorry
