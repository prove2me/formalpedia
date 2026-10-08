-- Prove2me | Theorems.Thm_BookProof_ChapterAtomicDecomposition_atomicPart_eq_sum_dirac
-- name    : BookProof.ChapterAtomicDecomposition.atomicPart_eq_sum_dirac
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:53:45.680536+00:00
-- url     : https://prove2.me/theorems/ad1fac89-fb28-44f9-8963-62f6e6975793
-- title:
--   `BookProof.ChapterAtomicDecomposition.atomicPart_eq_sum_dirac` (mu : Measure X) [SFinite mu] : atomicPart mu = Measure.sum (fun x : atoms mu => mu {(x : X)} • Measure.dirac (x : X)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAtomicDecomposition`.
--
--   `BookProof.ChapterAtomicDecomposition.atomicPart_eq_sum_dirac` (mu : Measure X) [SFinite mu] : atomicPart mu = Measure.sum (fun x : atoms mu => mu {(x : X)} • Measure.dirac (x : X))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAtomicDecomposition.atomicPart_eq_sum_dirac`.

-- Generated from ChapterAtomicDecomposition.lean — theorem BookProof.ChapterAtomicDecomposition.atomicPart_eq_sum_dirac
import Mathlib
import Definitions.Def_ChapterAtomicDecomposition
open BookProof.ChapterAtomicDecomposition


open MeasureTheory


variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

theorem BookProof.ChapterAtomicDecomposition.atomicPart_eq_sum_dirac (mu : Measure X) [SFinite mu] :
    atomicPart mu = Measure.sum (fun x : atoms mu => mu {(x : X)} • Measure.dirac (x : X)) := by sorry
